module Mask where

open import Basics
open import Ix
open import All
open import Cutting
open import Splitting
open import Perm
open import Interior
open import Recutter

module MASK {I}(C : I |> I) where

  open _|>_
  open INTERIOR C
  open RECUTTER C

  module CHOP {P}(pc : CutKit P)(rec : Recutter) where

    glue : (is : List I) -> (d : Subs is) ->
              All (Interior P) (subCollect is d) -> All (Interior P) is
    glue [] <> <> = <>
    glue (i ,- is) (inl <> , ds) (p , ps) = p , glue is ds ps
    glue (i ,- is) (inr c , ds) ps with isRiffle (slrs (inners C c) (subCollect is ds)) ps
    glue (i ,- is) (inr c , ds) .(riffle (slrs (inners C c) (subCollect is ds)) lp rp)
      | mkRiffle lp rp = < c 8>< lp > , glue is ds rp

    chop : (i : I)(c c' : Cuts C i) ->
           All (Interior P) (inners C c) -> All (Interior P) (inners C c')
    chops : (is : List I) -> All (Interior P) is -> (d : Subs is) ->
              All (Interior P) (subCollect is d)
    chop i c c' ps with rec i c c'
    ... | d , d' , m with chops (inners C c) ps d
    ... | qs = glue (inners C c') d' (permute m qs)
    chops [] <> <> = <>
    chops (i ,- is) (p , ps) (inl <> , ds) = p , chops is ps ds
    chops (i ,- is) (tile p , ps) (inr c' , ds) =
      cat (inners C c') (subCollect is ds) (all (\ _ -> tile) _ (pc i c' p)) (chops is ps ds)
    chops (i ,- is) (< c 8>< ps' > , ps) (inr c' , ds) =
      cat (inners C c') (subCollect is ds) (chop i c c' ps') (chops is ps ds)
    
    mask : forall {O Q} -> [ O -:> Interior P -:> Interior Q ]
                        -> [ Interior O -:> Interior P -:> Interior Q ]
    mask {O}{Q} f = ifold f help where
      help :  [ Cutting C (Interior P -:> Interior Q) -:> Interior P -:> Interior Q ]
      help i (c 8>< fs) (tile p) with pc i c p
      ... | ps = < c 8>< allAp (inners C c) fs (all (\ _ -> tile) _ ps) >
      help i (c 8>< fs) < c' 8>< ps > = < c 8>< allAp (inners C c) fs (chop i c' c ps) >
