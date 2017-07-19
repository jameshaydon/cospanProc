||| This example is adapted from the Go example:
||| https://talks.golang.org/2013/advconc.slide#6
module Examples.PingPong

import Types.Pushout as Ty
import ChannelContext
import PropProc

record Ball where
  constructor MkBall
  hits : Int

||| There is just one table called 'Table'
Table : Type
Table = ()

table : Table
table = ()

||| Make a channel for ping-pong balls.
TableCh : ChanCtx
TableCh = MkChanCtx Table (const Ball)

IdId : Morph TableCh TableCh
IdId = comp IdMorph IdMorph

||| A player takes a ball from the table, hits it, and put it back.
partial
player : String -> PropProc TableCh TableCh TableCh IdMorph IdMorph
player name = MkPropProc $
  Take table
       (\ball =>
           let ball' = record { hits $= (+ 1) } ball
           in LiftIO (putStrLn (name ++ " : " ++ show (hits ball')))
                     (Put table ball' Done))

||| The referee puts the ball on the table to start the game, and take it away
||| when it's finished.
referee : PropProc TableCh TableCh TableCh IdMorph IdMorph
referee = MkPropProc $
  Put table (MkBall 0)
      (Take table (\_ => Done))

||| The pushout we use: this is simply expressin the the aquare of id's is a
||| pushout diagram
pu : Pushout IdMorph IdMorph TableCh IdMorph IdMorph
pu = MkPushout (identityLeft Table Table id)

||| Two players playing together
pingPoing : PropProc TableCh TableCh TableCh IdMorph IdMorph
pingPoing = transfer p
  where
    p : PropProc TableCh TableCh TableCh IdId IdId
    p = propComp (player "pong") (player "ping") pu

||| Referee to start and stop the game.
game : PropProc TableCh TableCh TableCh IdMorph IdMorph
game = transfer p
  where
    p : PropProc TableCh TableCh TableCh IdId IdId
    p = propComp referee pingPoing pu

partial
export
main : IO ()
main = runner [()] game

-- TODO: introduce sleep to mimic go example better.
