{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts      #-}

module AppendProof where
import AppendImpl (append, map, concatMap, concatt, L(..), llen)
import Prelude hiding (map, concatMap)
import Language.Haskell.Liquid.ProofCombinators


prop_append_neutral :: L a -> Proof
{-@ prop_append_neutral :: xs:L a -> {append xs Emp == xs}  @-}
prop_append_neutral Emp        = trivial 
prop_append_neutral (_ ::: xs) = prop_append_neutral xs 


{-@ prop_assoc :: xs:L a -> ys:L a -> zs:L a
               -> {append (append xs ys) zs == append xs (append ys zs) } @-}
prop_assoc :: L a -> L a -> L a -> Proof
prop_assoc Emp _ _          = trivial
prop_assoc (x ::: xs) ys zs = prop_assoc xs ys zs



{-@ prop_map_append ::  f:(a -> a) -> xs:L a -> ys:L a
                    -> {map f (append xs ys) == append (map f xs) (map f ys) }
  @-}
prop_map_append :: (a -> a) -> L a -> L a -> Proof
prop_map_append f Emp        ys = trivial
prop_map_append f (_ ::: xs) ys = prop_map_append f xs ys 


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
