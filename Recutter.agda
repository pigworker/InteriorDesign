module Recutter where

open import Basics
open import All
open import Cutting
open import Perm

module RECUTTER {I}(C : I |> I) where

  open _|>_

  CutKit : (I -> Set) -> Set
  CutKit P = (i : I)(c : Cuts C i) -> P i -> All P (inners C c)

  Subs : List I -> Set
  Subs = All (\ i -> One + Cuts C i)
  subCollect : (is : List I) -> Subs is -> List I
  subCollect is cs = collect is (all (\ i -> (\ _ -> i ,- []) <+> inners C) is cs)

  Sub : I |> Sg I (Cuts C)
  Cuts   Sub (i , c) = Subs (inners C c)
  inners Sub {i , c} cs = subCollect (inners C c) cs

  Recutter : Set
  Recutter = (i : I)(c c' : Cuts C i) ->
             Sg (Cuts Sub (i , c)) \ d -> Sg (Cuts Sub (i , c')) \ d' ->
             inners Sub d ~ inners Sub d'
