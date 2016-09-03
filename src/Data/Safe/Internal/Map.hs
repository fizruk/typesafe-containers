{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Safe.Internal.Map where

import Data.Kind (Type, Constraint)
import GHC.TypeLits (TypeError, ErrorMessage(..))

import Data.Safe.Map.Schema

-- * 'Map' type

type Map schema = OrdMap (Unord schema)

-- ** Construction

empty :: Map '[]
empty = Empty

singleton :: Key k -> v -> Map '[ '(k, v) ]
singleton k v = Node k v empty

-- * Map with keys ordered

data OrdMap (schema :: Schema key) where
  Empty :: OrdMap '[]
  Node  :: Key k -> v -> OrdMap schema -> OrdMap ('(k, v) ': schema)

-- ** Ordered submaps

class OrdSubmap (sub :: Schema key) (schema :: Schema key) where
  submap :: OrdMap schema -> OrdMap sub

instance OrdSubmap '[] '[] where submap = id
instance OrdSubmap xs ys => OrdSubmap (p ': xs) (p ': ys) where submap (Node k v m) = Node k v (submap m)
instance OrdSubmap xs ys => OrdSubmap xs (y ': ys) where submap (Node k v m) = submap m
instance TypeError (Text "key " :<>: ShowType k :<>: Text " is missing")
  => OrdSubmap ('(k, v) ': schema) '[] where submap = error "impossible"

type HasPair k v schema = OrdSubmap '[ '(k, v) ] schema

-- ** Query

getPair :: forall k v schema. HasPair k v schema => Key k -> OrdMap schema -> (Key k, v)
getPair _ m = case submap m :: Map '[ '(k, v) ] of
  Node p v Empty -> (p, v)

get :: HasPair k v schema => Key k -> OrdMap schema -> v
get k = snd . getPair k

-- * Insertion

class CanInsert (k :: key) (v :: Type) (schema :: Schema key) where
  insert :: Key k -> v -> OrdMap schema -> OrdMap (Insert k v schema)

class CanInsert' (prepend :: Bool) (x :: key) (a :: Type) (schema :: Schema key) where
  insert' :: Key prepend -> Key x -> a -> OrdMap schema -> OrdMap (Insert x a schema)

instance (Insert x a schema ~ ('(x, a) ': schema)) => CanInsert' True x a schema
  where insert' _ = Node

instance (Insert x a ('(y, b) ': schema) ~ ('(y, b) ': Insert x a schema), CanInsert x a schema)
  => CanInsert' False x a ('(y, b) ': schema) where
    insert' _ x a (Node y b schema) = Node y b (insert x a schema)

instance CanInsert k v '[] where insert k v _ = singleton k v
instance CanInsert' (k < y) k v ('(y, b) ': schema) => CanInsert k v ('(y, b) ': schema) where
  insert = insert' (mkKey :: Key (k < y))

