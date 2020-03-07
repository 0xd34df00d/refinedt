{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}

module Idris.IdeModeClient
( typeCheck

, withIdris

, sendCommand
, readReply
) where

import qualified Data.ByteString.Char8 as BS
import Control.Exception
import Control.Monad.Operational
import Data.Default
import Data.String
import Data.String.Interpolate.IsString
import Data.Void
import Numeric
import System.IO(Handle, hPutStrLn, hGetLine)
import System.Process
import Text.Megaparsec
import Text.SExpression

newtype Command = Command { commandStr :: String } deriving (IsString)

data IdrisAction r where
  SendCommand :: Command -> IdrisAction ()
  ReadReply :: IdrisAction SExpr

type IdrisClient = Program IdrisAction

sendCommand :: Command -> IdrisClient ()
sendCommand = singleton . SendCommand

readReply :: IdrisClient SExpr
readReply = singleton ReadReply

typeCheck :: String -> Command
typeCheck ty = [i|((:type-of "#{ty}") 1)|]

parseIdrisResponse :: String -> Either (ParseErrorBundle String Void) SExpr
parseIdrisResponse = runParser (parseSExpr def <* eof) ""

withIdris :: IdrisClient r -> IO r
withIdris prog = bracket
  (runInteractiveCommand "idris --ide-mode")
  (\(stdin, stdout, stderr, ph) -> cleanupProcess (Just stdin, Just stdout, Just stderr, ph))
  (\(stdin, stdout, _, _) -> interpret stdin stdout prog)

interpret :: Handle -> Handle -> IdrisClient r -> IO r
interpret idrStdin idrStdout = go . view
  where
    go (Return val) = pure val
    go (act :>>= cont) = intAct act >>= go . view . cont

    intAct :: IdrisAction r -> IO r
    intAct (SendCommand cmd) = hPutStrLn idrStdin $ fmtLength cmd <> commandStr cmd
    intAct ReadReply = do
      countStr <- BS.unpack <$> BS.hGet idrStdout 6
      line <- BS.hGet idrStdout $ read $ "0x" <> countStr
      case parseIdrisResponse $ BS.unpack line of
           Right val -> pure val
           Left err -> error $ show err

fmtLength :: Command -> String
fmtLength cmd = replicate (6 - length hex) '0' <> hex
  where
    hex = showHex (length (commandStr cmd) + 1) ""
