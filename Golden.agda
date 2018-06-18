module Golden where

open import Basics
open import Vec
open import Ix
open import Cutting
open import Interior
open import Tensor
open RECTANGLE
open INTERIOR RectCut

ind : (n : Nat)(P : Nat -> Set) -> P zero ->
         ((k : Nat) -> P k -> P (suc k)) -> P n
ind zero P pz ps = pz
ind (suc n) P pz ps = ps n (ind n P pz ps)


+N-zero : (x : Nat) -> (x +N zero) == x
+N-zero x = ind x (\ x -> (x +N zero) == x) (refl _) (\ _ h -> refl suc =$= h)

+N-suc : (x y : Nat) -> (x +N suc y) == suc (x +N y)
+N-suc x y = ind x (\ x -> (x +N suc y) == suc (x +N y))
             (refl _) (\ _ h -> refl suc =$= h)


comm-+N : (x y : Nat) -> (x +N y) == (y +N x)
comm-+N x zero = +N-zero x
comm-+N x (suc y) rewrite +N-suc x y = refl suc =$= comm-+N x y


clockwise90 : {P : Nat * Nat -> Set}{w h : Nat} ->
  ({w h : Nat} -> P (w , h) -> P (h , w)) ->
  Interior P (w , h) -> Interior P (h , w)
clockwise90 pc90 (tile p) = tile (pc90 p)
clockwise90 pc90 < inl (l , r , refl _) 8>< (il , ir , <>) >
  = < inr (l , r , refl _) 8><
      clockwise90 pc90 il , clockwise90 pc90 ir , <> >
clockwise90 pc90 < inr (t , b , refl _) 8>< it , ib , <> >
  = < (inl (b , t , comm-+N b t)) 8><
      clockwise90 pc90 ib , clockwise90 pc90 it , <> >


Square : Nat * Nat -> Set
Square (w , h) = w == h

c90Sq : {w h : Nat} -> Square (w , h) -> Square (h , w)
c90Sq (refl _) = refl _

golden : (n : Nat) -> Sg Nat \ w -> Sg Nat \ h -> Interior Square (w , h)
golden zero = 1 , 1 , tile (refl 1)
golden (suc n) with golden n
... | w , h , i = (w +N h) , w , < (inl (w , h , refl _)) 8><
                  tile (refl w) , clockwise90 c90Sq i , <> >

fill : {n : Nat}{X : Set} -> X -> X -> X -> Vec X (suc (suc n))
fill {n} first midst last rewrite comm-+N 1 (suc n) = first ,- (pure midst +V (last ,- []))
  where open Applicative (VecAppl n)

border : {w h : Nat} -> Matrix Char (w , h)
border {w} {zero} = []
border {zero} {h} = pure [] where open Applicative (VecAppl _)
border {suc zero} {suc zero} = ('O' ,- []) ,- []
border {suc (suc w)} {suc zero} = fill '<' '-' '>' ,- []
border {suc zero} {suc (suc h)} = fill ('^' ,- []) ('|' ,- []) ('v' ,- [])
border {suc (suc w)} {suc (suc h)} =
  fill (fill '/' '-' '\\')
       (fill '|' ' ' '|')
       (fill '\\' '-' '/')

goldenInterior :  (n : Nat) -> Sg Nat \ w -> Sg Nat \ h -> Interior (Matrix Char) (w , h)
goldenInterior n with golden n
... | w , h , sqi = w , h , ifold (\ _ _ -> tile border) (\ _ -> <_>) (w , h) sqi


picture : [ Interior (Matrix Char) -:> Matrix Char ]
picture = ifold (\ _ -> id) NatCut2DMatAlg

goldenPicture : (n : Nat) -> Sg Nat \ w -> Sg Nat \ h -> Matrix Char (w , h)
goldenPicture n with goldenInterior n
... | w , h , mi = w , h , picture _ mi

