module Interior where

open import Basics
open import Ix
open import All
open import Cutting


module INTERIOR {I}(C : I |> I) where

  open _|>_ C

  data Interior (P : I -> Set)(i : I) : Set where
    tile : P i -> Interior P i
    <_>  : Cutting C (Interior P) i -> Interior P i

  ifold : forall {P Q} ->
          [ P -:> Q ] ->
          [ Cutting C Q -:> Q ] ->
          [ Interior P -:> Q ]
  ifolds : forall {P Q} ->
          [ P -:> Q ] ->
          [ Cutting C Q -:> Q ] ->
          [ All (Interior P) -:> All Q ]
  ifold pq cq i (tile p) = pq i p
  ifold pq cq i < c 8>< ps > = cq i (c 8>< ifolds pq cq _ ps)
  ifolds pq cq [] <> = <>
  ifolds pq cq (i ,- is) (x , xs) = ifold pq cq i x , ifolds pq cq is xs

  -- tile : [ P -:> Interior P ]

  extend : forall {P Q} ->
          [ P -:> Interior Q ] ->
          [ Interior P -:> Interior Q ]
  extend k = ifold k (\ i x -> < x >)

  -- and we have a monad, not in Set, but in I -> Set

open INTERIOR NatCut
{-
foo : Interior (\ n -> n == 3) 12
foo = < ((3 , 9 , refl _)) 8>< (tile (refl _) , {!!} , <>) >
-}
