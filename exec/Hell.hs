module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Maybe as Maybe
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import GHC.Types
import qualified Language.Haskell.Exts as HSE
import Language.Hell.Desugar
import Language.Hell.Evaluate
import Language.Hell.Inference
import Language.Hell.Parser
import Language.Hell.Term
import Language.Hell.Typecheck
import Language.Hell.Utils
import qualified Options.Applicative as Options
import Type.Reflection (typeRep, typeRepKind)
import qualified Type.Reflection as Type

------------------------------------------------------------------------------
-- Main entry point

data Command
  = Run FilePath
  | Check FilePath
  | Version
  | Exec String

main :: IO ()
main = dispatch =<< Options.execParser opts
  where
    opts =
      Options.info
        (commandParser Options.<**> Options.helper)
        ( Options.fullDesc
            <> Options.progDesc "Runs and typechecks Hell scripts"
            <> Options.header "hell - A Haskell-driven scripting language"
        )

commandParser :: Options.Parser Command
commandParser =
  Options.asum
    [ Run <$> Options.strArgument (Options.metavar "FILE" <> Options.help "Run the given .hell file")
    , Check <$> Options.strOption (Options.long "check" <> Options.metavar "FILE" <> Options.help "Typecheck the given .hell file")
    , Version <$ Options.flag () () (Options.long "version" <> Options.help "Print the version")
    , Exec <$> Options.strOption (Options.long "exec" <> Options.help "Execute the given expression" <> Options.metavar "EXPR")
    ]

dispatch :: Command -> IO ()
dispatch Version = putStrLn "2024-04-12"
dispatch (Run filePath) = do
  result <- parseFile filePath
  case result of
    Left e -> error $ e
    Right binds
      | anyCycles binds -> error "Cyclic bindings are not supported!"
      | otherwise ->
          case desugarAll binds of
            Left err -> error $ "Error desugaring! " ++ show err
            Right terms ->
              case lookup "main" terms of
                Nothing -> error "No main declaration!"
                Just main' ->
                  case inferExp mempty main' of
                    Left err -> error $ "Error inferring! " ++ show err
                    Right uterm ->
                      case check uterm Nil of
                        Left err -> error $ "Type checker error: " ++ show err
                        Right (Typed t ex) ->
                          case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                            Nothing -> error $ "Kind error, that's nowhere near an IO ()!"
                            Just Type.HRefl ->
                              case Type.eqTypeRep t (typeRep @(IO ())) of
                                Just Type.HRefl ->
                                  let action :: IO () = eval () ex
                                   in action
                                Nothing -> error $ "Type isn't IO (), but: " ++ show t
dispatch (Check filePath) = do
  result <- parseFile filePath
  case result of
    Left e -> error $ e
    Right binds
      | anyCycles binds -> error "Cyclic bindings are not supported!"
      | otherwise ->
          case desugarAll binds of
            Left err -> error $ "Error desugaring! " ++ show err
            Right terms ->
              case lookup "main" terms of
                Nothing -> error "No main declaration!"
                Just main' ->
                  case inferExp mempty main' of
                    Left err -> error $ "Error inferring! " ++ show err
                    Right uterm ->
                      case check uterm Nil of
                        Left err -> error $ "Type checker error: " ++ show err
                        Right (Typed t _ex) ->
                          case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                            Nothing -> error $ "Kind error, that's nowhere near an IO ()!"
                            Just Type.HRefl ->
                              case Type.eqTypeRep t (typeRep @(IO ())) of
                                Just Type.HRefl -> pure ()
                                Nothing -> error $ "Type isn't IO (), but: " ++ show t
dispatch (Exec string) = do
  case HSE.parseExpWithMode HSE.defaultParseMode {HSE.extensions = HSE.extensions HSE.defaultParseMode ++ [HSE.EnableExtension HSE.PatternSignatures, HSE.EnableExtension HSE.BlockArguments, HSE.EnableExtension HSE.TypeApplications]} string of
    HSE.ParseFailed _ e -> error $ e
    HSE.ParseOk e ->
      case desugarExp mempty e of
        Left err -> error $ "Error desugaring! " ++ show err
        Right uterm ->
          case inferExp mempty uterm of
            Left err -> error $ "Type inferer error! " ++ show err
            Right iterm ->
              case check iterm Nil of
                Left err -> error $ "Type checker error: " ++ show err
                Right (Typed t ex) ->
                  case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                    Nothing -> error $ "Kind error, that's nowhere near an IO ()!"
                    Just Type.HRefl ->
                      case Type.eqTypeRep t (typeRep @(IO ())) of
                        Just Type.HRefl ->
                          let action :: IO () = eval () ex
                           in action
                        Nothing -> error $ "Type isn't IO (), but: " ++ show t

--------------------------------------------------------------------------------
-- Parse with #!/shebangs

-- Parse a file into a list of decls, but strip shebangs.
parseFile :: String -> IO (Either String [(String, HSE.Exp HSE.SrcSpanInfo)])
parseFile filePath = do
  string <- ByteString.readFile filePath
  pure $ case HSE.parseModuleWithMode HSE.defaultParseMode {HSE.extensions = HSE.extensions HSE.defaultParseMode ++ [HSE.EnableExtension HSE.PatternSignatures, HSE.EnableExtension HSE.BlockArguments, HSE.EnableExtension HSE.TypeApplications]} (Text.unpack (dropShebang (Text.decodeUtf8 string))) >>= parseModule of
    HSE.ParseFailed _ e -> Left $ "Parse error: " <> e
    HSE.ParseOk binds -> Right binds

-- This should be quite efficient because it's essentially a pointer
-- increase. It leaves the \n so that line numbers are in tact.
dropShebang :: Text -> Text
dropShebang t = Maybe.fromMaybe t $ do
  rest <- Text.stripPrefix "#!" t
  pure $ Text.dropWhile (/= '\n') rest
