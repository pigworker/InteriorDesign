module Jumble where

open import Basics

swap : {I J : Set} -> I * J -> J * I
swap (i , j) = j , i

_+L_ : {X : Set} -> List X -> List X -> List X
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)
infixr 4 _+L_

catNatural : {X Y : Set}(f : X -> Y)(xs xs' : List X) ->
  (list f xs +L list f xs') == list f (xs +L xs')
catNatural f [] xs' = refl (list f xs')
catNatural f (x ,- xs) xs' = refl (f x ,-_) =$= catNatural f xs xs'

listlist : {X Y Z : Set}(f : Y -> Z)(g : X -> Y)(h : X -> Z)
  (q : (x : X) -> f (g x) == h x) ->
  (xs : List X) -> list f (list g xs) == list h xs
listlist f g h q [] = refl []
listlist f g h q (x ,- xs) = refl (_,-_) =$= q x =$= listlist f g h q xs

_-:>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> (I -> Set)
(S -:> T) i = S i -> T i
infixr 4 _-:>_

[_] : {I : Set} -> (I -> Set) -> Set
[ P ] = forall i -> P i

All : {X : Set} -> (X -> Set) -> (List X -> Set)
All P [] = One
All P (x ,- xs) = P x * All P xs

allPu : forall {X}{T : X -> Set} -> [ T ] -> [ All T ]
allPu t [] = <>
allPu t (x ,- xs) = t x , allPu t xs

allAp : forall {X}{S T : X -> Set} -> [ All (S -:> T) -:> All S -:> All T ]
allAp [] <> <> = <>
allAp (x ,- xs) (f , fs) (s , ss) = f s , allAp xs fs ss

all : {X : Set}{S T : X -> Set} ->
      [ S -:> T ] -> [ All S -:> All T ]
all f xs = allAp xs (allPu f xs)

allRe : forall {X Y}(f : X -> Y){P : Y -> Set}
        (xs : List X) -> All (\ x -> P (f x)) xs -> All P (list f xs)
allRe f [] <> = <>
allRe f (x ,- xs) (p , ps) = p , allRe f xs ps

collect : {I J : Set}(is : List I) -> All (\ i -> List J) is -> List J
collect [] <> = []
collect (i ,- is) (js , jss) = js +L collect is jss

allRePu : forall {X Y}(f : X -> Y){P : Y -> Set}(xs : List X)(g : [ P ]) ->
  allRe f xs (allPu (\ x -> g (f x)) xs) == allPu g (list f xs)
allRePu f [] g = refl <>
allRePu f (x ,- xs) g = refl (g (f x) ,_) =$= allRePu f xs g

all-Pu : forall {X}{S T : X -> Set}(f : [ S -:> T ])(s : [ S ])(xs : List X) ->
  all f xs (allPu s xs) == allPu (\ x -> f x (s x)) xs
all-Pu f s [] = refl <>
all-Pu f s (x ,- xs) = refl (f x (s x) ,_) =$= all-Pu f s xs

cart : forall {I J} -> List I -> List J -> List (I * J)
cart [] js = []
cart (i ,- is) js = list (i ,_) js +L cart is js


{-
all-grr : forall {X Y}{S : X -> Set}{T : Y -> Set}
  (f : X -> Y)(xs : List X)(g : [ S -:> (\ x -> T (f x)) ])(h : [ S ]) ->
  allAp (list f xs) (allPu g ?) (allRe f xs (allPu h xs)) ==
  ?
all-grr = ?
-}


data _<[_]>_ {X : Set} : List X -> List X -> List X -> Set where
  sz : [] <[ [] ]> []
  sl : forall {l ls ms rs} -> ls <[ ms ]> rs -> (l ,- ls) <[ l ,- ms ]> rs
  sr : forall {r ls ms rs} -> ls <[ ms ]> rs -> ls <[ r ,- ms ]> (r ,- rs)

riffle : {X : Set}{ls ms rs : List X} -> ls <[ ms ]> rs ->
         {P : X -> Set} -> All P ls -> All P rs -> All P ms
riffle sz <> <> = <>
riffle (sl x) (p , lp) rp = p , riffle x lp rp
riffle (sr x) lp (p , rp) = p , riffle x lp rp

srs : forall {X : Set}(xs : List X) -> [] <[ xs ]> xs
srs [] = sz
srs (x ,- xs) = sr (srs xs)

slrs : forall {X : Set}(xs ys : List X) -> xs <[ xs +L ys ]> ys
slrs [] ys = srs ys
slrs (x ,- xs) ys = sl (slrs xs ys)

cat : forall {X}{P : X -> Set}(xs ys : List X) -> All P xs -> All P ys -> All P (xs +L ys)
cat xs ys ps qs = riffle (slrs xs ys) ps qs

data IsRiffle {X : Set}{ls ms rs : List X}(i : ls <[ ms ]> rs){P : X -> Set}
  : All P ms -> Set where
  mkRiffle : (lp : All P ls)(rp : All P rs) -> IsRiffle i (riffle i lp rp)
isRiffle : {X : Set}{ls ms rs : List X}(i : ls <[ ms ]> rs){P : X -> Set}(mp : All P ms) -> IsRiffle i mp
isRiffle sz <> = mkRiffle <> <>
isRiffle (sl i) (p , mp) with isRiffle i mp
isRiffle (sl i) (p , .(riffle i lp rp)) | mkRiffle lp rp = mkRiffle (p , lp) rp
isRiffle (sr i) (p , mp) with isRiffle i mp
isRiffle (sr i) (p , .(riffle i lp rp)) | mkRiffle lp rp = mkRiffle lp (p , rp)

data _~_ {X : Set} : List X -> List X -> Set where
  [] : [] ~ []
  _,-_ : forall {x xs ys zs} -> (x ,- []) <[ ys ]> zs -> xs ~ zs -> (x ,- xs) ~ ys

permute : {X : Set}{xs ys : List X} -> xs ~ ys ->
          {P : X -> Set} -> All P xs -> All P ys
permute []        <> = <>
permute (i ,- is) (p , ps) = riffle i (p , <>) (permute is ps)

data SRS {X : Set}(ms : List X) : (xs : List X) -> [] <[ ms ]> xs -> Set where
  mkSRS : SRS ms ms (srs ms)

isSRS : {X : Set}{ms xs : List X}(i : [] <[ ms ]> xs) -> SRS ms xs i
isSRS sz = mkSRS
isSRS (sr i) with isSRS i
isSRS (sr .(srs _)) | mkSRS = mkSRS

mirror : {X : Set}{ls ms rs : List X} -> ls <[ ms ]> rs -> rs <[ ms ]> ls
mirror sz = sz
mirror (sl x) = sr (mirror x)
mirror (sr x) = sl (mirror x)

rotatel : {X : Set}{ls ms rs lrs rrs : List X} -> ls <[ ms ]> rs -> lrs <[ rs ]> rrs ->
  Sg (List X) \ ns -> (ls <[ ns ]> lrs) * (ns <[ ms ]> rrs)
rotatel sz sz = [] , sz , sz
rotatel (sl x) y with rotatel x y
... | _ , a , b = _ , sl a , sl b
rotatel (sr x) (sl y) with rotatel x y
... | _ , a , b = _ , sr a , sl b
rotatel (sr x) (sr y) with rotatel x y
... | _ , a , b = _ , a , sr b

rotater : {X : Set}{lls rls ls ms rs : List X} -> lls <[ ls ]> rls -> ls <[ ms ]> rs -> 
  Sg (List X) \ ns -> (lls <[ ms ]> ns) * (rls <[ ns ]> rs)
rotater x y with rotatel (mirror y) (mirror x)
... | _ , a , b = _ , mirror b , mirror a 


llswap : {X : Set}{ls ms lrs rrs : List X} ->
 (Sg (List X) \ rs -> (ls <[ ms ]> rs) * (lrs <[ rs ]> rrs)) ->
  Sg (List X) \ ns -> (lrs <[ ms ]> ns) * (ls <[ ns ]> rrs)
llswap (_ , x , y) with rotatel x y
... | _ , a , b = rotater (mirror a) b

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

_+L[] : {X : Set}(xs : List X) -> (xs +L []) == xs
[] +L[] = refl []
(x ,- xs) +L[] = refl (x ,-_) =$= (xs +L[])

assoc : {X : Set}(xs ys zs : List X) -> ((xs +L ys) +L zs) == (xs +L ys +L zs)
assoc [] ys zs = refl (ys +L zs)
assoc (x ,- xs) ys zs = refl (x ,-_) =$= assoc xs ys zs

insS : {X : Set}(xs : List X)(y : X)(zs : List X) -> (y ,- []) <[ (xs +L y ,- zs) ]> (xs +L zs)
insS [] y zs = sl (srs zs)
insS (x ,- xs) y zs = sr (insS xs y zs)

swapP : {X : Set}(xs ys : List X) -> (xs +L ys) ~ (ys +L xs)
swapP [] ys rewrite ys +L[] = reflP ys
swapP (x ,- xs) ys = insS ys x xs ,- swapP xs ys

catS : forall {X}{as abs bs cs cds ds : List X} ->
        as <[ abs ]> bs -> cs <[ cds ]> ds ->
        (as +L cs) <[ (abs +L cds) ]> (bs +L ds)
catS sz y = y
catS (sl x) y = sl (catS x y)
catS (sr x) y = sr (catS x y)

catP : forall {X : Set}{as bs cs ds : List X} -> as ~ cs -> bs ~ ds -> (as +L bs) ~ (cs +L ds)
catP [] q = q
catP (x ,- p) q = catS x (srs _) ,- catP p q

splimap : forall {X Y}(f : X -> Y){xs xys ys} -> xs <[ xys ]> ys ->
           list f xs <[ list f xys ]> list f ys
splimap f sz = sz
splimap f (sl s) = sl (splimap f s)
splimap f (sr s) = sr (splimap f s)

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
... | z rewrite assoc (list (i ,_) js) (list (_, j) is) (cart is js)
              | assoc (list (_, j) is) (list (i ,_) js) (cart is js)
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

record _|>_ (I O : Set) : Set1 where
  field
    Cuts   : O -> Set
    inners : {o : O} -> Cuts o -> List I

NatCut : Nat |> Nat
NatCut = record
  { Cuts = \ mn -> Sg Nat \ m -> Sg Nat \ n -> (m +N n) == mn
  ; inners = \ { (m , n , _) -> m ,- n ,- [] }
  }

module TENSOR where
  open _|>_
  _><_ : forall {I J} -> (I |> I) -> (J |> J) -> (I * J) |> (I * J)
  Cuts (C >< D) (i , j) = Cuts C i + Cuts D j
  inners (C >< D) {i , j} (inl c) = list (_, j) (inners C c)
  inners (C >< D) {i , j} (inr d) = list (i ,_) (inners D d)
open TENSOR

record Cutting {I O}(C : I |> O)(P : I -> Set)(o : O) : Set where
  constructor _8><_
  open _|>_ C
  field
    cut     : Cuts o
    pieces  : All P (inners cut)
infixr 3 _8><_
open Cutting public

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

  extend : forall {P Q} ->
          [ P -:> Interior Q ] ->
          [ Interior P -:> Interior Q ]
  extend k = ifold k (\ i x -> < x >)

  SubCut : (i : I)(c : Cuts i) -> Set
  SubCut i c = All (\ i -> One + Cuts i) (inners c)

  subCollect : (is : List I) -> All (\ i -> One + Cuts i) is -> List I
  subCollect is ds = collect is (all (\ i -> (\ _ -> i ,- []) <+> inners) is ds)

  subPieces : (i : I)(c : Cuts i) -> SubCut i c -> List I
  subPieces i c cs = subCollect (inners c) cs

  Recutter : Set
  Recutter = (i : I)(c c' : Cuts i) ->
             Sg (SubCut i c) \ d -> Sg (SubCut i c') \ d' ->
             subPieces i c d ~ subPieces i c' d'
             
  CutKit : (I -> Set) -> Set
  CutKit P = (i : I)(c : Cuts i) -> P i -> All P (inners c)

  module CHOP {P}(pc : CutKit P)(rec : Recutter) where

    glue : (is : List I) -> (d : All (\ i -> One + Cuts i) is) ->
              All (Interior P) (subCollect is d) -> All (Interior P) is
    glue [] <> <> = <>
    glue (i ,- is) (inl <> , ds) (p , ps) = p , glue is ds ps
    glue (i ,- is) (inr c , ds) ps with isRiffle (slrs (inners c) (subCollect is ds)) ps
    glue (i ,- is) (inr c , ds) .(riffle (slrs (inners c) (subCollect is ds)) lp rp)
      | mkRiffle lp rp = < c 8>< lp > , glue is ds rp

    chop : (i : I)(c c' : Cuts i)(ps : All (Interior P) (inners c)) -> All (Interior P) (inners c')
    chops : (is : List I) -> All (Interior P) is -> (d : All (\ i -> One + Cuts i) is) ->
              All (Interior P) (subCollect is d)
    chop i c c' ps with rec i c c'
    ... | d , d' , m with chops (inners c) ps d
    ... | qs = glue (inners c') d' (permute m qs)
    chops [] <> <> = <>
    chops (i ,- is) (p , ps) (inl <> , ds) = p , chops is ps ds
    chops (i ,- is) (tile p , ps) (inr c' , ds) =
      cat (inners c') (subCollect is ds) (all (\ _ -> tile) _ (pc i c' p)) (chops is ps ds)
    chops (i ,- is) (< c 8>< ps' > , ps) (inr c' , ds) = cat (inners c') (subCollect is ds)
                 (chop i c c' ps')
                 (chops is ps ds)

    mash : forall {Q} -> [ Interior (Interior P -:> Interior Q) -:> Interior P -:> Interior Q ]
    mash {Q} = ifold (\ i f -> f) help where
      help :  [ Cutting C (Interior P -:> Interior Q) -:> Interior P -:> Interior Q ]
      help i (c 8>< fs) (tile p) with pc i c p
      ... | ps = < c 8>< allAp (inners c) fs (all (\ _ -> tile) _ ps) >
      help i (c 8>< fs) < c' 8>< ps > = < c 8>< allAp (inners c) fs (chop i c' c ps) >

    mask : forall {O Q} -> [ O -:> Interior P -:> Interior Q ]
                        -> [ Interior O -:> Interior P -:> Interior Q ]
    mask {O}{Q} f = ifold f help where
      help :  [ Cutting C (Interior P -:> Interior Q) -:> Interior P -:> Interior Q ]
      help i (c 8>< fs) (tile p) with pc i c p
      ... | ps = < c 8>< allAp (inners c) fs (all (\ _ -> tile) _ ps) >
      help i (c 8>< fs) < c' 8>< ps > = < c 8>< allAp (inners c) fs (chop i c' c ps) >

  open CHOP public

  data Holey {I : Set}(P : I -> Set)(i : I) : Set where
    hole : Holey P i
    fill : P i -> Holey P i

  cutHole : forall {P : I -> Set} -> CutKit P -> CutKit (Holey P)
  cutHole f i c hole      = allPu (\ i -> hole) (inners c)
  cutHole f i c (fill p)  = all (\ _ -> fill) (inners c) (f i c p)

  superimpose : forall {P} -> CutKit P -> Recutter -> 
                [ Interior (Holey P) -:> Interior (Holey P) -:> Interior (Holey P) ]
  superimpose pc rec = mask (cutHole pc) rec \
    { i hole     y -> y
    ; i (fill x) y -> tile (fill x)
    }

open INTERIOR


module SUBCOLLECTLEMMA where

  open _|>_
  
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

open SUBCOLLECTLEMMA

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
cutCompare (suc x) x' (suc .(x +N suc d)) y' (suc n) xq yq | cutLt d (refl _) bq
  = cutLt d (refl _) bq
cutCompare (suc x) x' (suc .x) y' (suc n) xq yq | cutEq (refl _) bq = cutEq (refl _) bq
cutCompare (suc .(y +N suc d)) x' (suc y) y' (suc n) xq yq | cutGt d (refl _) bq = cutGt d (refl _) bq

NatRecut : Recutter NatCut
NatRecut n (a , b , qab) (c , d , qcd) with cutCompare a b c d n qab qcd
NatRecut n (a , b , qab) (c , d , qcd) | cutLt e q0 q1 =
  (inl <> , inr (suc e , d , q1) , <>) , (inr (a , suc e , q0) , inl <> , <>) , reflP _
NatRecut n (a , b , qab) (.a , .b , qcd) | cutEq (refl .a) (refl .b) =
  (inl <> , inl <> , <>) , (inl <> , inl <> , <>) , reflP _
NatRecut n (a , b , qab) (c , d , qcd) | cutGt e q0 q1 =
  (inr (c , suc e , q0) , inl <> , <>) , (inl <> , inr (suc e , b , q1) , <>) , reflP _

module TENSORRECUT  {I J}(C : I |> I)(D : J |> J)(rec : Recutter C)(red : Recutter D) where
  open _|>_

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

  fst (TensorRecut (i , j) (inl c) (inr d)) =
    allRe (_, j) (inners C c) (allPu (\ i -> inr (inr d)) (inners C c))
  fst (snd (TensorRecut (i , j) (inl c) (inr d))) =
    allRe (i ,_) (inners D d) (allPu (\ i -> inr (inl c)) (inners D d))
  snd (snd (TensorRecut (i , j) (inl c) (inr d)))
    rewrite cartLeftLemma (inners C c) j d
          | cartRightLemma i c (inners D d)
          = cartLemma (inners C c) (inners D d)
  fst (TensorRecut (i , j) (inr d) (inl c)) =
    allRe (i ,_) (inners D d) (allPu (\ i -> inr (inl c)) (inners D d))
  fst (snd (TensorRecut (i , j) (inr d) (inl c))) =
    allRe (_, j) (inners C c) (allPu (\ i -> inr (inr d)) (inners C c))
  snd (snd (TensorRecut (i , j) (inr d) (inl c)))
    rewrite cartLeftLemma (inners C c) j d
          | cartRightLemma i c (inners D d)
          = symP (cartLemma (inners C c) (inners D d))
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

open TENSORRECUT public

RectangleRecut : Recutter (NatCut >< NatCut)
RectangleRecut = TensorRecut NatCut NatCut NatRecut NatRecut
