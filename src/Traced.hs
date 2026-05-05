{-# LANGUAGE GADTs #-}

module Traced
  ( TracedA (..)
  , Traced
  , run
  )
where

-- | Traced arrow — a simple composable morphism with trace semantics.
-- This is a minimal implementation sufficient for SysL's interpreter.
-- In a full library this would be the free traced monoidal category.

data TracedA a b where
  Lift :: (a -> b) -> TracedA a b
  Compose :: TracedA b c -> TracedA a b -> TracedA a c

type Traced = TracedA

run :: Traced a b -> a -> b
run (Lift f) a = f a
run (Compose g f) a = run g (run f a)
