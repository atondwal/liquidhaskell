{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient8 where
import ReflectLib8
import Language.Haskell.Liquid.ProofCombinators

{-@ prop_concatMap :: f:(a -> L (L a)) -> xs:L a
                   -> { concatt (map f xs) == concatMap f xs }
  @-}
prop_concatMap :: (a -> L (L a)) -> L a -> Proof
prop_concatMap _ Emp        = trivial
prop_concatMap f (x ::: xs) = prop_concatMap f xs


{-
 /home/atondwal/src/liquidhaskell/benchmarks/popl18/ple/pos/lib/AppendImpl.hs:28:16: Error: GHC Error

 28 | {-@ axiomatize concatt @-}
                     ^

     Not in scope: variable or data constructor ` AppendImpl.x '

 -}

