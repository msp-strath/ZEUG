------------------------------------------------------------------------------
-----                                                                    -----
-----            dP            dP                                        -----
-----            88            88                                        -----
-----   88d888b. 88 .d8888b. d8888P dP    dP 88d888b. dP    dP .d8888b.  -----
-----   88'  `88 88 88'  `88   88   88    88 88'  `88 88    88 Y8ooooo.  -----
-----   88.  .88 88 88.  .88   88   88.  .88 88.  .88 88.  .88       88  -----
-----   88Y888P' dP `88888P8   dP   `8888P88 88Y888P' `88888P' `88888P'  -----
-----   88                               .88 88                          -----
-----   dP                           d8888P  dP                          -----
-----                                                                    -----
------------------------------------------------------------------------------

module Main where

import System.IO
import Utils
import Raw
import ProofState
import Command

version :: String
version = "1,000,000 years BC"

banner :: IO ()
banner = mapM_ putStrLn
  ["         dP            dP                                       "
  ,"         88            88                                       "
  ,"88d888b. 88 .d8888b. d8888P dP    dP 88d888b. dP    dP .d8888b. "
  ,"88'  `88 88 88'  `88   88   88    88 88'  `88 88    88 Y8ooooo. "
  ,"88.  .88 88 88.  .88   88   88.  .88 88.  .88 88.  .88       88 "
  ,"88Y888P' dP `88888P8   dP   `8888P88 88Y888P' `88888P' `88888P' "
  ,"88                               .88 88                         "
  ,"dP                           d8888P  dP                         "
  ,""
  ,"     version " ++ version
  ,""
  ]
  
main :: IO ()
main = do
  banner
  hSetBuffering stdin NoBuffering
  hSetBuffering stdout NoBuffering
  hSetEcho stdin False
  mainLoop B0 initialProofState True
  putStrLn "TATARANOO!"
  putStrLn ""

mainLoop ::  Bwd ProofState  -- history unto the dawn of time
         ->  ProofState      -- the present
         ->  Bool            -- is a redisplay necessary
         ->  IO ()           -- break stuff, go thud
mainLoop oldz new b = do
  if b then mapM_ putStrLn (display new) else return ()
  putStrLn ""
  putStr (prompt new ++ "> ")
  r <- rawIO
  putStrLn ""
  case r of
    RA "quit" -> return ()
    RA "undo" -> case oldz of
      B0 -> do
        putStrLn "Nothing to undo"
        mainLoop B0 new False
      oldz :< old -> mainLoop oldz old True
    c -> case command new c of
      (ss, m) -> mapM_ putStrLn ss >> case m of
        Just newer -> mainLoop (oldz :< new) newer True
        Nothing    -> mainLoop oldz new False
    _         -> mainLoop oldz new True
  -- mores stuff should happen here
