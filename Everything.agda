module Everything where

--The main module, contains the interface to SMB trees
open import SMBTree

-- The equational reasoning interface to SMB-trees
open import TreeAlgebra

-- Other modules used to develop it
--
-- Normal Brouwer trees with limits over any type
open import Brouwer
-- Maximum as a limit
open import LimMax
-- And inudctive definition of the maximum
open import IndMax
-- Solutions to indMax x x ≈ x
open import InfinityMax
