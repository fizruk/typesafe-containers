{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Safe.Internal.Map where

import Data.Kind (Type)
import Data.Semigroup
import Data.Monoid (Monoid(..))
import Data.Proxy
import GHC.TypeLits

import Data.Safe.Map.Schema

-- * 'Map' type

-- | A 'Map' with a fixed schema.
type Map schema = OrdMap (Unord schema)

-- ** Construction

-- | An empty 'Map'.
empty :: Map '[]
empty = Empty

-- | A singleton 'Map'.
singleton :: Key k -> v -> Map '[ '(k, v) ]
singleton k v = insert k v empty

-- * Map with keys ordered

-- | A map with keys ordered.
-- Ordered keys allow for faster type-level operations (like merging and inserting).
data OrdMap (schema :: Schema key) where
  Empty :: OrdMap '[]
  Node  :: Key k -> v -> OrdMap schema -> OrdMap ('(k, v) ': schema)

instance AllValues Eq schema => Eq (OrdMap schema) where
  Empty == Empty = True
  Node _ a xs == Node _ b ys = a == b && xs == ys

instance (AllValues Ord schema, AllValues Eq schema) => Ord (OrdMap schema) where
  Empty `compare` Empty = EQ
  Node _ a xs `compare` Node _ b ys = compare a b <> compare xs ys

instance AllValues Semigroup schema => Semigroup (OrdMap schema) where
  Empty <> Empty = Empty
  Node k a xs <> Node _ b ys = Node k (a <> b) (xs <> ys)

  stimes _ Empty = Empty
  stimes n (Node k a xs) = Node k (stimes n a) (stimes n xs)

instance Monoid (OrdMap '[]) where
  mempty = empty
  Empty `mappend` Empty = Empty

instance (Monoid v, Monoid (OrdMap schema)) => Monoid (OrdMap ('(k, v) ': schema)) where
  mempty = Node (mkKey :: Key k) mempty mempty
  Node k a xs `mappend` Node _ b ys = Node k (a `mappend` b) (xs `mappend` ys)

-- | Pretty print an 'OrdMap' given pretty printing function for keys.
-- This can be used to write 'Show' instances for 'OrdMap' with custom keys.
ppOrdMap :: (AllKeys kc schema, AllValues Show schema)
  => proxy kc -> (forall k. kc k => Key (k :: key) -> String) -> OrdMap (schema :: Schema key) -> String
ppOrdMap _ _ Empty = "empty"
ppOrdMap pkc ppKey (Node k v m) = ppOrdMap pkc ppKey m <> " & " <> ppKey k <> " =: " <> show v

instance Show (OrdMap '[]) where
  show _ = "empty"

instance (AllKeys KnownSymbol (p ': ps), AllValues Show (p ': ps)) => Show (OrdMap ((p ': ps) :: Schema Symbol)) where
  show = ppOrdMap (Proxy :: Proxy KnownSymbol) ppKey
    where
      ppKey k = "(mkKey :: Key " <> show (symbolVal k) <> ")"

instance (AllKeys KnownNat (p ': ps), AllValues Show (p ': ps)) => Show (OrdMap ((p ': ps) :: Schema Nat)) where
  show = ppOrdMap (Proxy :: Proxy KnownNat) ppKey
    where
      ppKey k = "(mkKey :: Key " <> show (natVal k) <> ")"

-- ** Ordered submaps

-- | Slice the 'OrdMap' to select only certain keys.
class OrdSubmap (sub :: Schema key) (schema :: Schema key) where
  submap :: OrdMap schema -> OrdMap sub

instance OrdSubmap '[] '[] where submap = id
instance {-# OVERLAPPING #-} OrdSubmap xs ys => OrdSubmap (p ': xs) (p ': ys) where submap (Node k v m) = Node k v (submap m)
instance OrdSubmap xs ys => OrdSubmap xs (y ': ys) where submap (Node _ _ m) = submap m
instance TypeError (Text "key " :<>: ShowType k :<>: Text " is missing")
  => OrdSubmap ('(k, v) ': schema) '[] where submap = error "impossible"

-- | A constraint ensuring that a @schema@ has the key @k@ with value type @v@.
type HasPair k v schema = (OrdSubmap '[ '(k, v) ] schema, Contains k v schema)

-- ** Query

-- | Extract a key-value pair from a 'Map'.
getPair :: forall k v schema. HasPair k v schema => Key k -> OrdMap schema -> (Key k, v)
getPair _ m = case submap m :: Map '[ '(k, v) ] of
  Node p v Empty -> (p, v)

-- | Extract a value for a given key.
get :: HasPair k v schema => Key k -> OrdMap schema -> v
get k = snd . getPair k

-- | A convenient alias for flipped 'get'.
(?:) :: HasPair k v schema => OrdMap schema -> Key k -> v
(?:) = flip get

-- * Insertion

class CanInsert (k :: key) (v :: Type) (schema :: Schema key) where
  -- | Insert a key-value pair into a 'Map'.
  insert :: Key k -> v -> OrdMap schema -> OrdMap (Insert k v schema)

instance CanInsert k v '[] where insert k v _ = Node k v empty
instance CanInsert' (Compare k y) k v ('(y, b) ': schema) => CanInsert k v ('(y, b) ': schema) where
  insert = insert' (Proxy :: Proxy (Compare k y))

class CanInsert' (cmp :: Ordering) (x :: key) (a :: Type) (schema :: Schema key) where
  insert' :: Proxy cmp -> Key x -> a -> OrdMap schema -> OrdMap (Insert x a schema)

instance (Insert x a schema ~ ('(x, a) ': schema)) => CanInsert' LT x a schema
  where insert' _ = Node

instance (Insert x a ('(y, b) ': schema) ~ ('(y, b) ': Insert x a schema), CanInsert x a schema)
  => CanInsert' GT x a ('(y, b) ': schema) where
    insert' _ x a (Node y b schema) = Node y b (insert x a schema)

-- | A convenient alias for 'insert'.
(=:) :: CanInsert k v schema => Key k -> v -> OrdMap schema -> OrdMap (Insert k v schema)
(=:) = insert
