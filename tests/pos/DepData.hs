
{-# LANGUAGE GADTs #-}

module DepData where

data Foo = Foo { thing1 :: Int, thing2 :: Int }

{-@ data Foo where
      Foo :: thing1:Int -> thing2:{v : Int | thing1 < v} -> Foo
  @-}

{- data Foo = Foo { thing1 :: Int, thing2 :: {v : Int | thing1 < v } } @-}

{-@ bog :: Foo -> Nat @-}
bog :: Foo -> Int
bog (Foo x y) = y - x
