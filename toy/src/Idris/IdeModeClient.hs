{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}

module Idris.IdeModeClient
( typeCheck

, withIdris

, sendCommand
, readReply
) where

import Control.Exception
import Control.Monad.Operational
import Data.Default
import Data.String
import Data.String.Interpolate.IsString
import Data.Void
import System.IO(Handle)
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
interpret = undefined
