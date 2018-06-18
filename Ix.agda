module Ix where

_-:>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> (I -> Set)
(S -:> T) i = S i -> T i
infixr 4 _-:>_

[_] : {I : Set} -> (I -> Set) -> Set
[ P ] = forall i -> P i
