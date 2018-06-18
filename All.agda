module All where

open import Basics
open import Ix

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
