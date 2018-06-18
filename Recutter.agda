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


module NATRECUT where

  open RECUTTER NatCut

  data CutCompare (x x' y y' n : Nat) : Set where
    cutLt : (d : Nat) -> (x +N suc d) == y -> (suc d +N y') == x' ->
      CutCompare x x' y y' n
    cutEq : x == y -> x' == y' ->
      CutCompare x x' y y' n
    cutGt : (d : Nat) -> (y +N suc d) == x -> (suc d +N x') == y' ->
      CutCompare x x' y y' n

  sucInj : {x y : Nat} -> suc x == suc y -> x == y
  sucInj (refl (suc _)) = refl _

  cutCompare : (x x' y y' n : Nat) -> (x +N x') == n -> (y +N y') == n ->
               CutCompare x x' y y' n
  cutCompare zero .n zero .n n (refl _) (refl _)
    = cutEq (refl _) (refl _)
  cutCompare zero .(suc (y +N y')) (suc y) y' .(suc (y +N y')) (refl _) (refl _)
    = cutLt y (refl _) (refl _)
  cutCompare (suc x) x' zero .(suc (x +N x')) .(suc (x +N x')) (refl _) (refl _)
    = cutGt x (refl _) (refl _)
  cutCompare (suc x) x' (suc y) y' zero () ()
  cutCompare (suc x) x' (suc y) y' (suc n) xq yq
    with cutCompare x x' y y' n (sucInj xq) (sucInj yq) 
  cutCompare (suc x) x' (suc .(x +N suc d)) y' (suc n) xq yq
    | cutLt d (refl _) bq = cutLt d (refl _) bq
  cutCompare (suc x) x' (suc .x) y' (suc n) xq yq
    | cutEq (refl _) bq = cutEq (refl _) bq
  cutCompare (suc .(y +N suc d)) x' (suc y) y' (suc n) xq yq
    | cutGt d (refl _) bq = cutGt d (refl _) bq

  NatRecut : Recutter
  NatRecut n (a , b , qab) (c , d , qcd) with cutCompare a b c d n qab qcd
  NatRecut n (a , b , qab) (c , d , qcd) | cutLt e q0 q1
    = (inl <> , inr (suc e , d , q1) , <>)
    , (inr (a , suc e , q0) , inl <> , <>)
    , reflP _
  NatRecut n (a , b , qab) (.a , .b , qcd) | cutEq (refl .a) (refl .b)
    = (inl <> , inl <> , <>)
    , (inl <> , inl <> , <>)
    , reflP _
  NatRecut n (a , b , qab) (c , d , qcd) | cutGt e q0 q1
    = (inr (c , suc e , q0) , inl <> , <>)
    , (inl <> , inr (suc e , b , q1) , <>)
    , reflP _

module SUBCOLLECTLEMMA where

  open _|>_
  open RECUTTER

  subCollectLemma : forall {I J}(C : I |> I)(D : J |> J)
                    (f : I -> J)(g : (i : I) -> Cuts C i -> Cuts D (f i)) ->
                    (q : (i : I)(c : Cuts C i) -> inners D (g i c) == list f (inners C c)) ->
                    (is : List I)(ps : All (\ i -> One + Cuts C i) is) ->
                    subCollect D (list f is) (allRe f is (all (\ i -> id +map g i) is ps)) ==
                    list f (subCollect C is ps)
  subCollectLemma C D f g q [] <> = refl []
  subCollectLemma C D f g q (i ,- is) (inl <> , ps) =
    refl (f i ,-_) =$= subCollectLemma C D f g q is ps
  subCollectLemma C D f g q (i ,- is) (inr c , ps) = 
    (inners D (g i c) +L
     subCollect D (list f is) (allRe f is (allAp is (allPu (\ i -> id +map g i) is) ps)))
      =[ refl _+L_ =$= q i c =$= subCollectLemma C D f g q is ps >=
    (list f (inners C c) +L list f (subCollect C is ps))
      =[ catNatural f (inners C c) (subCollect C is ps) >=
    list f (inners C c +L subCollect C is ps)
      [QED]

