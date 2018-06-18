module Splitting where

open import Basics
open import All

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

data SRS {X : Set}(ms : List X) : (xs : List X) -> [] <[ ms ]> xs -> Set where
  mkSRS : SRS ms ms (srs ms)

isSRS : {X : Set}{ms xs : List X}(i : [] <[ ms ]> xs) -> SRS ms xs i
isSRS sz = mkSRS
isSRS (sr i) with isSRS i
isSRS (sr .(srs _)) | mkSRS = mkSRS

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

insS : {X : Set}(xs : List X)(y : X)(zs : List X) -> (y ,- []) <[ (xs +L y ,- zs) ]> (xs +L zs)
insS [] y zs = sl (srs zs)
insS (x ,- xs) y zs = sr (insS xs y zs)

catS : forall {X}{as abs bs cs cds ds : List X} ->
        as <[ abs ]> bs -> cs <[ cds ]> ds ->
        (as +L cs) <[ (abs +L cds) ]> (bs +L ds)
catS sz y = y
catS (sl x) y = sl (catS x y)
catS (sr x) y = sr (catS x y)

splimap : forall {X Y}(f : X -> Y){xs xys ys} -> xs <[ xys ]> ys ->
           list f xs <[ list f xys ]> list f ys
splimap f sz = sz
splimap f (sl s) = sl (splimap f s)
splimap f (sr s) = sr (splimap f s)
