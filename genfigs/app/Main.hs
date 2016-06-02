module Main where

import Lib
import System.IO
import Control.Monad.Writer
import Text.Printf

xLeader, x1, x2 :: Int
x1      = 1000
xLeader = 3000
x2      = 5000

tellCoords :: Int -> Int -> Int -> Int -> Writer String ()
tellCoords x1 y1 x2 y2 = tell $ printf "\t %d %d %d %d\n" x1 y1 x2 y2

tellTimeline :: Int -> Int -> Writer String ()
tellTimeline n x = do
  tell "2 1 0 1 0 7 50 -1 -1 0.000 0 0 -1 0 0 2\n"
  tellCoords x y x (y + timelineLen)
  tell "2 1 0 1 0 7 50 -1 -1 0.000 0 0 -1 0 0 2\n"
  tellCoords (x - halfHeaderWidth) y (x + halfHeaderWidth) y

  where
  halfHeaderWidth = 700
  y = timelineStart n

tellRPC :: Int -> Int -> Int -> (Int -> Writer String ()) -> Writer String Int
tellRPC xHandler yStart halfRTT tellLabel = do
  tell "2 1 0 1 0 7 50 -1 -1 0.000 0 0 7 1 0 2\n"
  tell "\t1 1 1.00 60.00 60.00\n"
  tellCoords xLeader yStart xHandler (yStart + halfRTT)
  tellLabel (yStart + halfRTT)
  tell "2 1 0 1 0 7 50 -1 -1 0.000 0 0 7 1 0 2\n"
  tell "\t1 1 1.00 60.00 60.00\n"
  tellCoords xHandler (yStart + halfRTT + procTime)
             xLeader  (yStart + 2 * halfRTT + procTime)
  return $ yStart + 2 * halfRTT + 2 * procTime

timelineSpacing :: Int
timelineSpacing = 500

timelineLen :: Int
timelineLen = 6500

timelineStart n = (timelineLen + timelineSpacing) * n

labelOffset :: Int
labelOffset = 60

procTime :: Int
procTime = 50

propSpacing :: Int
propSpacing = 290

tellPrepare :: Int -> String -> String -> Writer String Int
tellPrepare yStart ballot era = tellRPC x1 yStart 620 $ \labelY -> tell $ printf
  "4 2 0 50 -1 0 12 0.0000 2 180 1890 935 %d $\\\\mathbf{prepare}(%s)$ (quorum from $Q_{%s}$)\\001\n"
  (labelY + labelOffset) ballot era

tellPropose :: Int -> String -> String -> String -> Writer String Int
tellPropose yStart inst ballot era = tellRPC x2 yStart 350 $ \labelY -> tell $ printf
  "4 0 0 50 -1 0 12 0.0000 2 180 2160 5105 %d $\\\\mathbf{proposed}_{%s}(%s)$ (quorum from $Q_{%s}$)\\001\n"
  (labelY + labelOffset) inst ballot era

main :: IO ()
main = writeFile "test.fig" $ execWriter $ do
  tell $ unlines
    [ "#FIG 3.2  Produced by xfig version 3.2.5c"
    , "Landscape"
    , "Center"
    , "Metric"
    , "A4      "
    , "100.00"
    , "Single"
    , "-2"
    , "1200 2"
    ]

  mapM_ (tellTimeline 0) [xLeader, x1, x2]
  mapM_ (tellTimeline 1) [xLeader, x1, x2]

  tellStoppable  (100 + timelineStart 0)
  tellSmooth     (100 + timelineStart 1)

tellSmooth firstPrepareStartTime = do
  firstPrepareFinishTime <- tellPrepare firstPrepareStartTime "b" "e"

  finishTimes <- forM [0..3] $ \n -> tellPropose (firstPrepareFinishTime + propSpacing * n)
    (if n == 0 then "i" else printf "i+%d" n) "b" "e"

  let secondPrepareStartTime = last finishTimes
  secondPrepareFinishTime <- tellPrepare secondPrepareStartTime "b'" "e+1"

  forM_ [4..12] $ \n -> let
    proposeStartTime = firstPrepareFinishTime + propSpacing * n
    in tellPropose proposeStartTime
          (printf "i+%d" n)
          (if proposeStartTime >= secondPrepareFinishTime then "b'" else "b")
          "e+1"

tellStoppable firstPrepareStartTime = do
  firstPrepareFinishTime <- tellPrepare firstPrepareStartTime  "b" "e"

  finishTimes <- forM [0..3] $ \n -> tellPropose (firstPrepareFinishTime + propSpacing * n)
    (if n == 0 then "i" else printf "i+%d" n) "b" "e"
  let secondPrepareStartTime = last finishTimes
  secondPrepareFinishTime <- tellPrepare secondPrepareStartTime "b'" "e+1"

  forM_ [4..7] $ \n -> tellPropose (secondPrepareFinishTime + propSpacing * (n - 4))
    (printf "i+%d" n) "b'" "e + 1"

