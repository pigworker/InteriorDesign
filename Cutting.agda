module Cutting where

open import Basics
open import Ix
open import All

record _|>_ (I O : Set) : Set1 where
  field
    Cuts   : O -> Set
    inners : {o : O} -> Cuts o -> List I

NatCut : Nat |> Nat
NatCut = record
  { Cuts   = \ mn -> Sg Nat \ m -> Sg Nat \ n -> (m +N n) == mn
  ; inners = \ { (m , n , _) -> m ,- n ,- [] }
  }

record Cutting {I O}(C : I |> O)(P : I -> Set)(o : O) : Set where
  constructor _8><_
  open _|>_ C
  field
    cut     : Cuts o
    pieces  : All P (inners cut)
infixr 3 _8><_
open Cutting public

