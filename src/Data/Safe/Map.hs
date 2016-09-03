module Data.Safe.Map (
  -- * 'Map' type
  Map,

  -- * Query
  get,
  (?:),
  getPair,

  -- * Construction
  empty,
  singleton,

  -- * Insertion
  insert,
  (=:),
) where

import Data.Safe.Internal.Map
