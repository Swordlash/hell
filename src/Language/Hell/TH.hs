module Language.Hell.TH where

import qualified Control.Concurrent as Concurrent
import Control.Monad
import Data.Bifunctor
import qualified Data.Bool as Bool
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Builder as ByteString hiding (writeFile)
import qualified Data.ByteString.Lazy as L
import qualified Data.Either as Either
import qualified Data.Eq as Eq
import qualified Data.Function as Function
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Ord as Ord
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Language.Haskell.TH (Q)
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import Language.Hell.IRep
import Language.Hell.Typecheck
import Language.Hell.UTerm
import qualified System.Directory as Dir
import System.Environment
import System.Exit
import qualified System.IO as IO
import System.Process.Typed as Process
import qualified System.Timeout as Timeout
import qualified Text.Show as Show
import Type.Reflection (SomeTypeRep (..), typeRep, pattern TypeRep)
import qualified UnliftIO.Async as Async

--------------------------------------------------------------------------------
-- Supported type constructors

supportedTypeConstructors :: Map String SomeTypeRep
supportedTypeConstructors =
  Map.fromList
    [ ("Bool", SomeTypeRep $ typeRep @Bool)
    , ("Int", SomeTypeRep $ typeRep @Int)
    , ("Char", SomeTypeRep $ typeRep @Char)
    , ("Text", SomeTypeRep $ typeRep @Text)
    , ("ByteString", SomeTypeRep $ typeRep @ByteString)
    , ("ExitCode", SomeTypeRep $ typeRep @ExitCode)
    , ("Maybe", SomeTypeRep $ typeRep @Maybe)
    , ("Either", SomeTypeRep $ typeRep @Either)
    , ("IO", SomeTypeRep $ typeRep @IO)
    , ("ProcessConfig", SomeTypeRep $ typeRep @ProcessConfig)
    ]

--------------------------------------------------------------------------------
-- Support primitives

--------------------------------------------------------------------------------
-- UTF-8 specific operations without all the environment gubbins
--
-- Much better than what Data.Text.IO provides

t_setStdin :: Text -> ProcessConfig () () () -> ProcessConfig () () ()
t_setStdin text = setStdin (byteStringInput (L.fromStrict (Text.encodeUtf8 text)))

t_readProcess :: ProcessConfig () () () -> IO (ExitCode, Text, Text)
t_readProcess c = do
  (code, out, err) <- b_readProcess c
  pure (code, Text.decodeUtf8 out, Text.decodeUtf8 err)

t_readProcess_ :: ProcessConfig () () () -> IO (Text, Text)
t_readProcess_ c = do
  (out, err) <- b_readProcess_ c
  pure (Text.decodeUtf8 out, Text.decodeUtf8 err)

t_readProcessStdout_ :: ProcessConfig () () () -> IO Text
t_readProcessStdout_ c = do
  out <- b_readProcessStdout_ c
  pure (Text.decodeUtf8 out)

t_putStrLn :: Text -> IO ()
t_putStrLn = ByteString.hPutBuilder IO.stdout . (<> "\n") . ByteString.byteString . Text.encodeUtf8

t_hPutStr :: IO.Handle -> Text -> IO ()
t_hPutStr h = ByteString.hPutBuilder h . ByteString.byteString . Text.encodeUtf8

t_putStr :: Text -> IO ()
t_putStr = t_hPutStr IO.stdout

t_getLine :: IO Text
t_getLine = fmap Text.decodeUtf8 ByteString.getLine

t_writeFile :: Text -> Text -> IO ()
t_writeFile fp t = ByteString.writeFile (Text.unpack fp) (Text.encodeUtf8 t)

t_appendFile :: Text -> Text -> IO ()
t_appendFile fp t = ByteString.appendFile (Text.unpack fp) (Text.encodeUtf8 t)

t_readFile :: Text -> IO Text
t_readFile fp = fmap Text.decodeUtf8 (ByteString.readFile (Text.unpack fp))

--------------------------------------------------------------------------------
-- ByteString operations

b_readProcess :: ProcessConfig () () () -> IO (ExitCode, ByteString, ByteString)
b_readProcess c = do
  (code, out, err) <- readProcess c
  pure (code, L.toStrict out, L.toStrict err)

b_readProcess_ :: ProcessConfig () () () -> IO (ByteString, ByteString)
b_readProcess_ c = do
  (out, err) <- readProcess_ c
  pure (L.toStrict out, L.toStrict err)

b_readProcessStdout_ :: ProcessConfig () () () -> IO ByteString
b_readProcessStdout_ c = do
  out <- readProcessStdout_ c
  pure (L.toStrict out)

supportedLits :: Map String (UTerm ())
supportedLits =
  Map.fromList
    [ -- Text I/O
      ("Text.putStrLn", lit t_putStrLn)
    , ("Text.hPutStr", lit t_hPutStr)
    , ("Text.putStr", lit t_putStr)
    , ("Text.getLine", lit t_getLine)
    , ("Text.writeFile", lit t_writeFile)
    , ("Text.readFile", lit t_readFile)
    , ("Text.appendFile", lit t_appendFile)
    , ("Text.readProcess", lit t_readProcess)
    , ("Text.readProcess_", lit t_readProcess_)
    , ("Text.readProcessStdout_", lit t_readProcessStdout_)
    , ("Text.setStdin", lit t_setStdin)
    , -- Text operations
      ("Text.eq", lit ((==) @Text))
    , ("Text.length", lit Text.length)
    , ("Text.concat", lit Text.concat)
    , ("Text.breakOn", lit Text.breakOn)
    , ("Text.lines", lit Text.lines)
    , ("Text.words", lit Text.words)
    , ("Text.unlines", lit Text.unlines)
    , ("Text.unwords", lit Text.unwords)
    , ("Text.intercalate", lit Text.intercalate)
    , ("Text.reverse", lit Text.reverse)
    , ("Text.toLower", lit Text.toLower)
    , ("Text.toUpper", lit Text.toUpper)
    , -- Needs Char operations.
      -- ("Text.any", lit Text.any),
      -- ("Text.all", lit Text.all),
      -- ("Text.filter", lit Text.filter),
      ("Text.take", lit Text.take)
    , ("Text.splitOn", lit Text.splitOn)
    , ("Text.takeEnd", lit Text.takeEnd)
    , ("Text.drop", lit Text.drop)
    , ("Text.stripPrefix", lit Text.stripPrefix)
    , ("Text.stripSuffix", lit Text.stripSuffix)
    , ("Text.isSuffixOf", lit Text.isSuffixOf)
    , ("Text.isPrefixOf", lit Text.isPrefixOf)
    , ("Text.dropEnd", lit Text.dropEnd)
    , ("Text.strip", lit Text.strip)
    , ("Text.replace", lit Text.replace)
    , ("Text.isPrefixOf", lit Text.isPrefixOf)
    , ("Text.isSuffixOf", lit Text.isSuffixOf)
    , ("Text.isInfixOf", lit Text.isInfixOf)
    , -- Int operations
      ("Int.show", lit (Text.pack . show @Int))
    , ("Int.eq", lit ((==) @Int))
    , ("Int.plus", lit ((+) @Int))
    , ("Int.subtract", lit (subtract @Int))
    , -- Bytes I/O
      ("ByteString.hGet", lit ByteString.hGet)
    , ("ByteString.hPutStr", lit ByteString.hPutStr)
    , ("ByteString.readProcess", lit b_readProcess)
    , ("ByteString.readProcess_", lit b_readProcess_)
    , ("ByteString.readProcessStdout_", lit b_readProcessStdout_)
    , -- Handles, buffering
      ("IO.stdout", lit IO.stdout)
    , ("IO.stderr", lit IO.stderr)
    , ("IO.stdin", lit IO.stdin)
    , ("IO.hSetBuffering", lit IO.hSetBuffering)
    , ("IO.NoBuffering", lit IO.NoBuffering)
    , ("IO.LineBuffering", lit IO.LineBuffering)
    , ("IO.BlockBuffering", lit IO.BlockBuffering)
    , -- Concurrent stuff
      ("Concurrent.threadDelay", lit Concurrent.threadDelay)
    , -- Bool
      ("Bool.True", lit Bool.True)
    , ("Bool.False", lit Bool.False)
    , ("Bool.not", lit Bool.not)
    , -- Get arguments
      ("Environment.getArgs", lit $ fmap (map Text.pack) getArgs)
    , ("Environment.getEnvironment", lit $ fmap (map (bimap Text.pack Text.pack)) getEnvironment)
    , ("Environment.getEnv", lit $ fmap Text.pack . getEnv . Text.unpack)
    , -- Current directory
      ("Directory.createDirectoryIfMissing", lit (\b f -> Dir.createDirectoryIfMissing b (Text.unpack f)))
    , ("Directory.createDirectory", lit (Dir.createDirectory . Text.unpack))
    , ("Directory.getCurrentDirectory", lit (fmap Text.pack Dir.getCurrentDirectory))
    , ("Directory.listDirectory", lit (fmap (fmap Text.pack) . Dir.listDirectory . Text.unpack))
    , ("Directory.setCurrentDirectory", lit (Dir.setCurrentDirectory . Text.unpack))
    , ("Directory.renameFile", lit (\x y -> Dir.renameFile (Text.unpack x) (Text.unpack y)))
    , ("Directory.copyFile", lit (\x y -> Dir.copyFile (Text.unpack x) (Text.unpack y)))
    , -- Process
      ("Process.proc", lit $ \n xs -> proc (Text.unpack n) (map Text.unpack xs))
    , ("Process.setEnv", lit $ Process.setEnv @() @() @() . map (bimap Text.unpack Text.unpack))
    , ("Process.runProcess", lit $ runProcess @IO @() @() @())
    , ("Process.runProcess_", lit $ runProcess_ @IO @() @() @())
    , -- Lists
      ("List.and", lit (List.and @[]))
    , ("List.or", lit (List.or @[]))
    ]

--------------------------------------------------------------------------------
-- Derive prims TH

polyLits :: Map String (Forall, [TH.Uniq], IRep TH.Uniq)
polyLits =
  Map.fromList
    $( let -- Derive well-typed primitive forms.
           derivePrims :: Q TH.Exp -> Q TH.Exp
           derivePrims m = do
            e <- m
            case e of
              TH.DoE Nothing binds -> do
                TH.listE $ map makePrim binds
              _ -> error $ "Expected plain do-notation, but got: " ++ show e

           nameUnique (TH.Name _ (TH.NameU i)) = i
           nameUnique _ = error "Bad TH problem in nameUnique."

           toTy :: TH.Type -> Q TH.Exp
           toTy = \case
            TH.AppT (TH.AppT TH.ArrowT f) x -> [|IFun $(toTy f) $(toTy x)|]
            TH.AppT f x -> [|IApp $(toTy f) $(toTy x)|]
            TH.ConT name -> [|ICon (SomeTypeRep $(TH.appTypeE (TH.varE 'typeRep) (TH.conT name)))|]
            TH.VarT a -> [|IVar $(TH.litE $ TH.IntegerL $ nameUnique a)|]
            TH.ListT -> [|ICon (SomeTypeRep (typeRep @[]))|]
            TH.TupleT 2 -> [|ICon (SomeTypeRep (typeRep @(,)))|]
            TH.TupleT 3 -> [|ICon (SomeTypeRep (typeRep @(,,)))|]
            TH.TupleT 4 -> [|ICon (SomeTypeRep (typeRep @(,,,)))|]
            TH.TupleT 0 -> [|ICon (SomeTypeRep (typeRep @()))|]
            t -> error $ "Uexpected type shape: " ++ show t

           -- Make a well-typed primitive form. Expects a very strict format.
           makePrim :: TH.Stmt -> Q TH.Exp
           makePrim
            ( TH.NoBindS
                ( TH.SigE
                    (TH.AppE (TH.LitE (TH.StringL string)) expr)
                    (TH.ForallT vars constraints typ)
                  )
              ) =
              let constrained = foldl getConstraint mempty constraints
                  vars0 =
                    map
                      ( \case
                          (TH.PlainTV v TH.SpecifiedSpec) -> TH.litE $ TH.IntegerL $ nameUnique v
                          _ -> error "The type variable isn't what I expected."
                      )
                      vars
                  ordEqShow = Set.fromList [''Ord, ''Eq, ''Show]
                  monadics = Set.fromList [''Functor, ''Applicative, ''Monad]
                  builder =
                    foldr
                      ( \case
                          (TH.PlainTV v TH.SpecifiedSpec) -> \rest ->
                            TH.appE
                              ( TH.conE
                                  ( case Map.lookup v constrained of
                                      Nothing -> 'NoClass
                                      Just constraints'
                                        | Set.isSubsetOf constraints' ordEqShow -> 'OrdEqShow
                                        | Set.isSubsetOf constraints' monadics -> 'Monadic
                                      _ -> error "I'm not sure what to do with this variable."
                                  )
                              )
                              ( TH.lamE
                                  [pure $ TH.ConP 'TypeRep [TH.VarT v] []]
                                  rest
                              )
                          _ -> error "Did not expect this type of variable!"
                      )
                      [|Final $ typed $(TH.sigE (pure expr) (pure typ))|]
                      vars
               in [|(string, ($builder, $(TH.listE vars0), $(toTy typ)))|]
           makePrim e = error $ "Should be of the form \"Some.name\" The.name :: T\ngot: " ++ show e

           -- Just tells us whether a given variable is constrained by a
           -- type-class or not.
           getConstraint m (TH.AppT (TH.ConT cls') (TH.VarT v)) =
            Map.insertWith Set.union v (Set.singleton cls') m
           getConstraint _ _ = error "Bad constraint!"
        in derivePrims
            [|
              do
                -- Operators
                "$" (Function.$) :: forall a b. (a -> b) -> a -> b
                "." (Function..) :: forall a b c. (b -> c) -> (a -> b) -> a -> c
                -- Monad
                "Monad.bind" (Prelude.>>=) :: forall m a b. (Monad m) => m a -> (a -> m b) -> m b
                "Monad.then" (Prelude.>>) :: forall m a b. (Monad m) => m a -> m b -> m b
                "Monad.return" return :: forall a m. (Monad m) => a -> m a
                -- Monadic operations
                "Monad.mapM_" mapM_ :: forall a m. (Monad m) => (a -> m ()) -> [a] -> m ()
                "Monad.forM_" forM_ :: forall a m. (Monad m) => [a] -> (a -> m ()) -> m ()
                "Monad.mapM" mapM :: forall a b m. (Monad m) => (a -> m b) -> [a] -> m [b]
                "Monad.forM" forM :: forall a b m. (Monad m) => [a] -> (a -> m b) -> m [b]
                "Monad.when" when :: forall m. (Monad m) => Bool -> m () -> m ()
                -- IO
                "IO.mapM_" mapM_ :: forall a. (a -> IO ()) -> [a] -> IO ()
                "IO.forM_" forM_ :: forall a. [a] -> (a -> IO ()) -> IO ()
                "IO.pure" pure :: forall a. a -> IO a
                "IO.print" (t_putStrLn . Text.pack . Show.show) :: forall a. (Show a) => a -> IO ()
                "Timeout.timeout" Timeout.timeout :: forall a. Int -> IO a -> IO (Maybe a)
                -- Show
                "Show.show" (Text.pack . Show.show) :: forall a. (Show a) => a -> Text
                -- Eq/Ord
                "Eq.eq" (Eq.==) :: forall a. (Eq a) => a -> a -> Bool
                "Ord.lt" (Ord.<) :: forall a. (Ord a) => a -> a -> Bool
                "Ord.gt" (Ord.>) :: forall a. (Ord a) => a -> a -> Bool
                -- Tuples
                "Tuple.(,)" (,) :: forall a b. a -> b -> (a, b)
                "Tuple.(,)" (,) :: forall a b. a -> b -> (a, b)
                "Tuple.(,,)" (,,) :: forall a b c. a -> b -> c -> (a, b, c)
                "Tuple.(,,,)" (,,,) :: forall a b c d. a -> b -> c -> d -> (a, b, c, d)
                -- Exceptions
                "Error.error" (error . Text.unpack) :: forall a. Text -> a
                -- Bool
                "Bool.bool" Bool.bool :: forall a. a -> a -> Bool -> a
                -- Function
                "Function.id" Function.id :: forall a. a -> a
                "Function.fix" Function.fix :: forall a. (a -> a) -> a
                -- Lists
                "List.cons" (:) :: forall a. a -> [a] -> [a]
                "List.nil" [] :: forall a. [a]
                "List.length" List.length :: forall a. [a] -> Int
                "List.concat" List.concat :: forall a. [[a]] -> [a]
                "List.drop" List.drop :: forall a. Int -> [a] -> [a]
                "List.take" List.take :: forall a. Int -> [a] -> [a]
                "List.map" List.map :: forall a b. (a -> b) -> [a] -> [b]
                "List.lookup" List.lookup :: forall a b. (Eq a) => a -> [(a, b)] -> Maybe b
                "List.sort" List.sort :: forall a. (Ord a) => [a] -> [a]
                "List.reverse" List.reverse :: forall a. [a] -> [a]
                "List.sortOn" List.sortOn :: forall a b. (Ord b) => (a -> b) -> [a] -> [a]
                -- Maybe
                "Maybe.maybe" Maybe.maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
                "Maybe.Nothing" Maybe.Nothing :: forall a. Maybe a
                "Maybe.Just" Maybe.Just :: forall a. a -> Maybe a
                "Maybe.listToMaybe" Maybe.listToMaybe :: forall a. [a] -> Maybe a
                -- Either
                "Either.either" Either.either :: forall a b x. (a -> x) -> (b -> x) -> Either a b -> x
                "Either.Left" Either.Left :: forall a b. a -> Either a b
                "Either.Right" Either.Right :: forall a b. b -> Either a b
                -- Async
                "Async.concurrently" Async.concurrently :: forall a b. IO a -> IO b -> IO (a, b)
                "Async.race" Async.race :: forall a b. IO a -> IO b -> IO (Either a b)
                "Async.pooledMapConcurrently_" Async.pooledMapConcurrently_ :: forall a. (a -> IO ()) -> [a] -> IO ()
                "Async.pooledForConcurrently_" Async.pooledForConcurrently_ :: forall a. [a] -> (a -> IO ()) -> IO ()
                "Async.pooledMapConcurrently" Async.pooledMapConcurrently :: forall a b. (a -> IO b) -> [a] -> IO [b]
                "Async.pooledForConcurrently" Async.pooledForConcurrently :: forall a b. [a] -> (a -> IO b) -> IO [b]
              |]
     )
