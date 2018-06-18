module Perm where

open import Basics
open import All
open import Splitting

data _~_ {X : Set} : List X -> List X -> Set where
  [] : [] ~ []
  _,-_ : forall {x xs ys zs} -> (x ,- []) <[ ys ]> zs -> xs ~ zs -> (x ,- xs) ~ ys

permute : {X : Set}{xs ys : List X} -> xs ~ ys ->
          {P : X -> Set} -> All P xs -> All P ys
permute []        <> = <>
permute (i ,- is) (p , ps) = riffle i (p , <>) (permute is ps)

reflP : {X : Set}(xs : List X) -> xs ~ xs
reflP [] = []
reflP (x ,- xs) = sl (srs xs) ,- reflP xs

insP : forall {X : Set}{x : X}{xs xs' ys ys'} -> (x ,- []) <[ xs' ]> xs -> (x ,- []) <[ ys' ]> ys
         -> xs ~ ys -> xs' ~ ys'
insP (sl i) j p with isSRS i
insP (sl .(srs _)) j p | mkSRS = j ,- p
insP (sr i) j (k ,- p) =
  let  _ , k' , j' = llswap (_ , j , k)
  in   k' ,- insP i j' p

l2r : forall {X : Set}{x : X}{xs xs' ys'}(i : (x ,- []) <[ xs' ]> xs)(p' : xs' ~ ys') ->
  Sg (List X) \ ys -> Sg ((x ,- []) <[ ys' ]> ys) \ j -> xs ~ ys
l2r (sl i) (j ,- p) with isSRS i
l2r (sl .(srs _)) (j ,- p) | mkSRS = _ , j , p
l2r (sr i) (k' ,- p') with l2r i p'
... | _ , j' , p with llswap (_ , k' , j')
... | _ , j , k = _ , j , (k ,- p)

transP : {X : Set}{xs ys zs : List X} -> xs ~ ys -> ys ~ zs -> xs ~ zs
transP [] [] = []
transP (i ,- p) q' with l2r i q'
... | _ , j , q = j ,- transP p q

symP : {X : Set}{xs ys : List X} -> xs ~ ys -> ys ~ xs
symP [] = []
symP (i ,- p) = insP i (sl (srs _)) (symP p)

swapP : {X : Set}(xs ys : List X) -> (xs +L ys) ~ (ys +L xs)
swapP [] ys rewrite ys +L[] = reflP ys
swapP (x ,- xs) ys = insS ys x xs ,- swapP xs ys

catP : forall {X : Set}{as bs cs ds : List X} -> as ~ cs -> bs ~ ds -> (as +L bs) ~ (cs +L ds)
catP [] q = q
catP (x ,- p) q = catS x (srs _) ,- catP p q

permap : forall {X Y}(f : X -> Y){xs xs' : List X} -> xs ~ xs' -> list f xs ~ list f xs'
permap f [] = []
permap f (x ,- p) = splimap f x ,- permap f p

cartNil : forall {I}(is : List I){J} -> cart {J = J} is [] == []
cartNil [] = refl []
cartNil (i ,- is) = cartNil is

cartCons : forall {I J}(is : List I)(j : J)(js : List J) ->
  cart is (j ,- js) ~ (list (_, j) is +L cart is js)
cartCons [] j js = []
cartCons (i ,- is) j js with catP (swapP (list (i ,_) js) (list (_, j) is)) (reflP (cart is js))
... | z rewrite assoc+L (list (i ,_) js) (list (_, j) is) (cart is js)
              | assoc+L (list (_, j) is) (list (i ,_) js) (cart is js)
  =
  (sl (srs (list (_, j) is +L cart (i ,- is) js))) ,-
  transP (catP (reflP (list (i ,_) js)) (cartCons is j js))
    z

cartLemma : forall {I J}(is : List I)(js : List J) ->
  cart is js ~ list swap (cart js is)
cartLemma {I}{J} [] js rewrite cartNil js {I} = []
cartLemma {I}{J} (i ,- is) js with catP (reflP (list (i ,_) js)) (cartLemma is js)
... | z rewrite sym (listlist swap (_, i) (i ,_) (\ j ->  refl (i , j)) js)
              | catNatural swap (list (_, i) js) (cart js is)
  = transP
  z
  (symP (permap (\ ji -> snd ji , fst ji) (cartCons js i is)))
