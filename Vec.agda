module Vec where

open import Basics

data Vec (X : Set) : Nat -> Set where
  [] : Vec X zero
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

record Applicative (F : Set -> Set) : Set1 where
  field
    pure : {X : Set} -> X -> F X
    _<*>_ : {S T : Set} -> F (S -> T) -> F S -> F T
  infixl 2 _<*>_

VecAppl : (n : Nat) -> Applicative \ X -> Vec X n
Applicative.pure (VecAppl zero)    x = []
Applicative.pure (VecAppl (suc n)) x = x ,- Applicative.pure (VecAppl n) x
Applicative._<*>_ (VecAppl .zero)    []        []        = []
Applicative._<*>_ (VecAppl .(suc _)) (f ,- fs) (s ,- ss) =
  f s ,- Applicative._<*>_ (VecAppl _) fs ss

module VTRAVERSE {F}(A : Applicative F) where

  open Applicative A

  vtraverse : forall {n S T} -> (S -> F T) -> Vec S n -> F (Vec T n)
  vtraverse f []        = pure []
  vtraverse f (s ,- ss) = pure _,-_ <*> f s <*> vtraverse f ss

Matrix : Set -> Nat * Nat -> Set
Matrix X (i , j) = Vec (Vec X i) j

xpose : forall {X ij} -> Matrix X ij -> Matrix X (swap ij)
xpose = vtraverse id where
  open VTRAVERSE (VecAppl _)

