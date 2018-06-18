module Holey where

open import Basics
open import Ix
open import All
open import Cutting
open import Interior
open import Recutter
open import Mask

module HOLEY {I}(C : I |> I) where

  open _|>_ C
  open INTERIOR C
  open RECUTTER C
  open MASK C

  data Holey {I : Set}(P : I -> Set)(i : I) : Set where
    hole : Holey P i
    fill : P i -> Holey P i

  module SUPERIMPOSE {P}(pc : CutKit P)(rec : Recutter) where

    cutHole : CutKit (Holey P)
    cutHole i c hole      = allPu (\ i -> hole) (inners c)
    cutHole i c (fill p)  = all (\ _ -> fill) (inners c) (pc i c p)

    open CHOP cutHole rec

    superimpose : [ Interior (Holey P) -:> Interior (Holey P) -:> Interior (Holey P) ]
    superimpose = mask \
      { i hole     y -> y
      ; i (fill x) y -> tile (fill x)
      }
  
  
