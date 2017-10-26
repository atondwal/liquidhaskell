{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectLib8 where

{-@ axiomatize concatt @-}
concatt :: L (L a) -> L a
concatt Emp      = Emp
concatt (x:::xs) = append x (concatt xs)

data L a = Emp | a ::: L a
{-@ data L [llen] a = Emp | (:::) {x::a, xs :: L a } @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (_ ::: xs) = 1 + llen xs

