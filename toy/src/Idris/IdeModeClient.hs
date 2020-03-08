{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs, KindSignatures #-}

module Idris.IdeModeClient
( sendCommand
, readReply
, typeCheck

, withIdris
, startIdris
, stopIdris
, runIdrisClient
) where

import qualified Data.ByteString.Char8 as BS
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Operational
import Data.Default
import Data.String
import Data.String.Interpolate.IsString
import Data.Void
import Numeric
import System.IO(Handle, hPutStrLn, hFlush)
import System.Process
import Text.Megaparsec
import Text.SExpression

newtype Command = Command { commandStr :: String } deriving (IsString)

data IdrisAction :: (Type -> Type) -> Type -> Type where
  SendCommand :: Command -> IdrisAction m ()
  ReadReply :: IdrisAction m SExpr

type IdrisClientT m = ProgramT (IdrisAction m) m

sendCommand :: Command -> IdrisClientT m ()
sendCommand = singleton . SendCommand

readReply :: IdrisClientT m SExpr
readReply = singleton ReadReply

typeCheck :: String -> Command
typeCheck ty = [i|((:type-of "#{ty}") 1)|]

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

runIdrisClient :: MonadIO m => IdrisHandle -> IdrisClientT m r -> m r
runIdrisClient (IdrisHandle (idrStdin, idrStdout, _, _)) = viewT >=> go
  where
    go (Return val) = pure val
    go (act :>>= cont) = intAct act >>= viewT . cont >>= go

    intAct :: MonadIO m => IdrisAction r -> m r
    intAct (SendCommand cmd) = do
      liftIO $ hPutStrLn idrStdin $ fmtLength cmd <> commandStr cmd
      liftIO $ hFlush idrStdin
    intAct ReadReply = liftIO $ do
      countStr <- BS.unpack <$> BS.hGet idrStdout 6
      line <- BS.hGet idrStdout $ read $ "0x" <> countStr
      case parseIdrisResponse $ BS.unpack line of
           Right val -> pure val
           Left err -> error $ show err

fmtLength :: Command -> String
fmtLength cmd = replicate (6 - length hex) '0' <> hex
  where
    hex = showHex (length (commandStr cmd) + 1) ""
