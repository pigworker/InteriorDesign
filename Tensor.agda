module Tensor where

open import Basics
open import Ix
open import All
open import Perm
open import Cutting
open import Recutter

open _|>_
open RECUTTER
open SUBCOLLECTLEMMA

_><_ : forall {I J} -> (I |> I) -> (J |> J) -> (I * J) |> (I * J)
Cuts (C >< D) (i , j) = Cuts C i + Cuts D j
inners (C >< D) {i , j} (inl c) = list (_, j) (inners C c)
inners (C >< D) {i , j} (inr d) = list (i ,_) (inners D d)

module TENSORRECUT  {I J}(C : I |> I)(D : J |> J)(rec : Recutter C)(red : Recutter D) where

  cartLeftLemma : (is : List I)(j : J)(d : Cuts D j) -> subCollect (C >< D) (list (_, j) is)
                (allRe (_, j) is
                   (allPu (\ _ -> inr (inr d)) is)) == cart is (inners D d)
  cartLeftLemma [] j d = refl []
  cartLeftLemma (i ,- is) j d = refl (list (i ,_) (inners D d) +L_) =$= cartLeftLemma is j d

  cartRightLemma : (i : I)(c : Cuts C i)(js : List J) ->
     subCollect (C >< D) (list (i ,_) js)
                 (allRe (i ,_) js (allPu (\ _ -> inr (inl c)) js)) ==
                 list swap (cart js (inners C c))
  cartRightLemma i c [] = refl []
  cartRightLemma i c (j ,- js)
    rewrite sym (catNatural swap (list (j ,_) (inners C c)) (cart js (inners C c)))
                | listlist swap (j ,_) (_, j) (\ i -> refl (i , j)) (inners C c)
                = refl (list (_, j) (inners C c) +L_) =$= cartRightLemma i c js

  TensorRecut : Recutter (C >< D)

  -- both cuts in left dimension
  TensorRecut (i , j) (inl c) (inl c') with rec i c c'
  ... | x , y , m
      = allRe (_, j) (inners C c) (all (\ _ -> id +map inl) _ x)
      , allRe (_, j) (inners C c') (all (\ _ -> id +map inl) _ y)
      , lemma where
        lemma : subCollect (C >< D) (list (_, j) (inners C c))
                 (allRe (_, j) (inners C c) (all (\ _ -> id +map inl) (inners C c) x))
                ~
                subCollect (C >< D) (list (_, j) (inners C c'))
                 (allRe (_, j) (inners C c') (all (\ _ -> id +map inl) (inners C c') y))
        lemma rewrite subCollectLemma C (C >< D) (_, j) (\ _ -> inl) (\ i c -> refl _)
                        (inners C c) x
                    | subCollectLemma C (C >< D) (_, j) (\ _ -> inl) (\ i c -> refl _)
                        (inners C c') y
          = permap (_, j) m

  -- left to right
  fst (TensorRecut (i , j) (inl c) (inr d)) =
    allRe (_, j) (inners C c) (allPu (\ i -> inr (inr d)) (inners C c))
  fst (snd (TensorRecut (i , j) (inl c) (inr d))) =
    allRe (i ,_) (inners D d) (allPu (\ i -> inr (inl c)) (inners D d))
  snd (snd (TensorRecut (i , j) (inl c) (inr d)))
    rewrite cartLeftLemma (inners C c) j d
          | cartRightLemma i c (inners D d)
          = cartLemma (inners C c) (inners D d)

  -- right to left
  fst (TensorRecut (i , j) (inr d) (inl c)) =
    allRe (i ,_) (inners D d) (allPu (\ i -> inr (inl c)) (inners D d))
  fst (snd (TensorRecut (i , j) (inr d) (inl c))) =
    allRe (_, j) (inners C c) (allPu (\ i -> inr (inr d)) (inners C c))
  snd (snd (TensorRecut (i , j) (inr d) (inl c)))
    rewrite cartLeftLemma (inners C c) j d
          | cartRightLemma i c (inners D d)
          = symP (cartLemma (inners C c) (inners D d))

  -- both cuts in right dimension
  TensorRecut (i , j) (inr d) (inr d') with red j d d'
  ... | x , y , m
    = allRe (i ,_) (inners D d) (all (\ _ -> id +map inr) _ x)
    , allRe (i ,_) (inners D d') (all (\ _ -> id +map inr) _ y)
    , lemma where
        lemma : subCollect (C >< D) (list (i ,_) (inners D d))
                 (allRe (i ,_) (inners D d) (all (\ _ -> id +map inr) (inners D d) x))
                ~
                subCollect (C >< D) (list (i ,_) (inners D d'))
                 (allRe (i ,_) (inners D d') (all (\ _ -> id +map inr) (inners D d') y))
        lemma rewrite subCollectLemma D (C >< D) (i ,_) (\ _ -> inr) (\ i d -> refl _)
                        (inners D d) x
                    | subCollectLemma D (C >< D) (i ,_) (\ _ -> inr) (\ i d -> refl _)
                        (inners D d') y
                    = permap (i ,_) m

module RECTANGLE where

  RectCut = NatCut >< NatCut

  open NATRECUT
  open TENSORRECUT NatCut NatCut NatRecut NatRecut

  RectRecut = TensorRecut

