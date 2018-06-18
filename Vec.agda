module Vec where

open import Basics
open import Ix
open import All
open import Cutting
open import Tensor

data Vec (X : Set) : Nat -> Set where
  [] : Vec X zero
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

_+V_ : forall {X n m} -> Vec X n -> Vec X m -> Vec X (n +N m)
[]        +V ys = ys
(x ,- xs) +V ys = x ,- (xs +V ys)

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

module VECALL {I : Set}{P : I -> Set}{n : Nat}where

  open Applicative (VecAppl n)
  
  vecAll : {is : List I} ->
         All (\ i -> Vec (P i) n) is -> Vec (All P is) n
  vecAll {[]} pss = pure <>
  vecAll {i ,- is} (ps , pss) = pure _,_ <*> ps <*> vecAll pss

  VecLiftAlg : (C : I |> I) ->
             Algebra (Cutting C) P ->
             Algebra (Cutting C) (\ i -> Vec (P i) n)
  VecLiftAlg C alg i (c 8>< pss) = pure (alg i << (c 8><_)) <*> vecAll pss

open VECALL

NatCutVecAlg : {X : Set} -> Algebra (Cutting NatCut) (Vec X)
NatCutVecAlg {X} .(m +N n) (m , n , refl .(m +N n) 8>< xm , xn , <>) = xm +V xn

open RECTANGLE

NatCut2DMatAlg : {X : Set} -> Algebra (Cutting RectCut) (Matrix X)
NatCut2DMatAlg _ (inl c 8>< ms) = VecLiftAlg NatCut NatCutVecAlg _ (c 8>< ms) 
NatCut2DMatAlg _ (inr c 8>< ms) = NatCutVecAlg _ (c 8>< ms)

