{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Safe.Map.Schema where

import Data.Kind (Type, Constraint)
import GHC.TypeLits (Symbol, Nat, CmpSymbol, CmpNat)
import GHC.OverloadedLabels

-- | A schema for a map-like container.
type Schema key = [(key, Type)]

-- | The key constructor for the map.
-- This is essentially just a proxy.
data Key k = Key

instance (s ~ k) => IsLabel (s :: Symbol) (Key k) where
  fromLabel _ = Key

-- | Create a key.
mkKey :: Key k
mkKey = Key

type family AllKeys (c :: key -> Constraint) (schema :: Schema key) :: Constraint where
  AllKeys c '[] = ()
  AllKeys c ('(k, v) ': schema) = (c k, AllKeys c schema)

type family AllValues (c :: Type -> Constraint) (schema :: Schema key) :: Constraint where
  AllValues c '[] = ()
  AllValues c ('(k, v) ': schema) = (c v, AllValues c schema)

type family Contains (k :: key) (v :: Type) (schema :: Schema key) :: Constraint where
  Contains k v ('(k, u) ': schema) = (v ~ u)
  Contains k v (_ ': schema) = Contains k v schema

-- | Delete a key from a 'Schema'.
type family DeleteKey (k :: key) (schema :: Schema key) :: Schema key where
  DeleteKey k '[] = '[]
  DeleteKey k ('(k, v) ': schema) = schema
  DeleteKey k ('(x, v) ': schema) = DeleteKey k schema

-- | Insert a key in a 'Schema' preserving the order of the keys.
-- If the key is already present with the same value type then @schema@ remains unchanged.
type family Insert (k :: key) (v :: Type) (schema :: Schema key) :: Schema key where
  Insert k v '[] = '[ '(k, v) ]
  Insert k v ('(k, v) ': schema) = '(k, v) ': schema
  Insert k v ('(x, y) ': schema) = If (k > x) ('(x, y) ': Insert k v schema) ('(k, v) ': '(x, y) ': schema)

-- | Merge two sorted 'Schema's.
type family Merge (s :: Schema key) (t :: Schema key) :: Schema key where
  Merge '[] schema = schema
  Merge schema '[] = schema
  Merge ('(x, a) ': xs) ('(y, b) ': ys)
    = If (x < y)
        ('(x, a) ': Merge xs ('(y, b) ': ys))
        ('(y, b) ': Merge ('(x, a) ': xs) ys)

-- | Sort the keys of a 'Schema' using insertion sort.
type family SortKeys (schema :: Schema key) :: Schema key where
  SortKeys '[] = '[]
  SortKeys ('(k, v) : schema) = Insert k v (SortKeys schema)

type Unord schema = SortKeys schema

-- | Compare two types.
type family Compare (x :: k1) (y :: k2) :: Ordering

type instance Compare (x :: Symbol) (y :: Symbol) = CmpSymbol x y
type instance Compare (x :: Nat)    (y :: Nat)    = CmpNat    x y

-- | A type-level case for 'Ordering'.
type family CaseOrdering o l e g where
  CaseOrdering LT l e g = l
  CaseOrdering EQ l e g = e
  CaseOrdering GT l e g = g

type x <  y = CaseOrdering (Compare x y) True  False False
type x <= y = CaseOrdering (Compare x y) True  True  False
type x == y = CaseOrdering (Compare x y) False True  False
type x /= y = CaseOrdering (Compare x y) True  False True
type x >= y = CaseOrdering (Compare x y) False True  True
type x >  y = CaseOrdering (Compare x y) False False True

-- | A type-level @if .. then .. else ..@ block.
type family If (cond :: Bool) t f where
  If True  t f = t
  If False t f = f
