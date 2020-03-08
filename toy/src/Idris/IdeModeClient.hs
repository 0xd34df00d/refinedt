{-# LANGUAGE QuasiQuotes, RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs, KindSignatures #-}

module Idris.IdeModeClient
( sendCommand
, readReply
, withFile
, write

, typeCheck
, loadFile

, withIdris
, startIdris
, stopIdris
, runIdrisClient
) where

import qualified Data.ByteString.Char8 as BS
import Control.Exception(bracket)
import Control.Monad
import Control.Monad.Catch(MonadMask)
import Control.Monad.IO.Class
import Control.Monad.Operational
import Data.Default
import Data.Kind
import Data.String
import Data.String.Interpolate.IsString
import Data.Void
import Numeric
import System.IO(Handle, hPutStrLn, hFlush)
import System.IO.Temp
import System.Process
import Text.Megaparsec
import Text.SExpression

newtype Command = Command { commandStr :: String } deriving (IsString)

data File = File
  { handle :: Handle
  , path :: FilePath
  }

data IdrisAction :: (Type -> Type) -> Type -> Type where
  SendCommand :: Command -> IdrisAction m ()
  ReadReply :: IdrisAction m SExpr
  Write :: File -> String -> IdrisAction m ()
  WithFile :: (File -> IdrisClientT m r) -> IdrisAction m r

type IdrisClientT m = ProgramT (IdrisAction m) m

sendCommand :: Command -> IdrisClientT m ()
sendCommand = singleton . SendCommand

readReply :: IdrisClientT m SExpr
readReply = singleton ReadReply

write :: File -> String -> IdrisClientT m ()
write f s = singleton $ Write f s

withFile :: (File -> IdrisClientT m r) -> IdrisClientT m r
withFile = singleton . WithFile

typeCheck :: String -> Command
typeCheck ty = [i|((:type-of "#{ty}") 1)|]

loadFile :: File -> Command
loadFile file = [i|((:load-file "#{path file}") 1)|]

parseIdrisResponse :: String -> Either (ParseErrorBundle String Void) SExpr
parseIdrisResponse = runParser (parseSExpr def <* eof) ""

withIdris :: IdrisClientT IO r -> IO r
withIdris prog = bracket
  startIdris
  stopIdris
  (`runIdrisClient` prog)

checkVersion :: Monad m => IdrisClientT m ()
checkVersion = do
  reply <- readReply
  case reply of
       List [Atom ":protocol-version", Number 1, Number 0] -> pure ()
       _ -> error "Unknown protocol"

newtype IdrisHandle = IdrisHandle (Handle, Handle, Handle, ProcessHandle)

startIdris :: IO IdrisHandle
startIdris = do
  ih <- IdrisHandle <$> runInteractiveCommand "idris --ide-mode"
  runIdrisClient ih checkVersion
  pure ih

stopIdris :: IdrisHandle -> IO ()
stopIdris (IdrisHandle (stdin, stdout, stderr, ph)) = cleanupProcess (Just stdin, Just stdout, Just stderr, ph)

runIdrisClient :: (MonadMask m, MonadIO m) => IdrisHandle -> IdrisClientT m r -> m r
runIdrisClient ih@(IdrisHandle (idrStdin, idrStdout, _, _)) = viewT >=> go
  where
    go (Return val) = pure val
    go (act :>>= cont) = intAct act >>= viewT . cont >>= go

    intAct :: (MonadMask m, MonadIO m) => IdrisAction m r -> m r
    intAct (SendCommand cmd) = do
      liftIO $ hPutStrLn idrStdin $ fmtLength cmd <> commandStr cmd
      liftIO $ hFlush idrStdin
    intAct ReadReply = liftIO $ do
      countStr <- BS.unpack <$> BS.hGet idrStdout 6
      line <- BS.hGet idrStdout $ read $ "0x" <> countStr
      case parseIdrisResponse $ BS.unpack line of
           Right val -> pure val
           Left err -> error $ show err
    intAct (Write f s) = liftIO $ hPutStrLn (handle f) s
    intAct (WithFile act) = withSystemTempFile "toy-idris" $ \path handle -> runIdrisClient ih $ act File { .. }

fmtLength :: Command -> String
fmtLength cmd = replicate (6 - length hex) '0' <> hex
  where
    hex = showHex (length (commandStr cmd) + 1) ""
