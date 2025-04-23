module notions where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
  using (_≡_; refl)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat.Properties as ℕₚ
open import Relation.Nullary.Decidable using (map)
open import Data.Sum using (_⊎_; inj₁; inj₂)


data ⊥ : Set where

~ : Set
  → Set
~ A
  = A → ⊥

_and_ : Bool → Bool → Bool
_and_ true x = x
_and_ false x = false


_or_ : Bool → Bool → Bool
false or b = b
true or b = true 

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

not : Bool → Bool
not true = false
not false = true 

if_then : {A : Set} → Bool → Bool → Bool
if false then x = not x
if true then x = x 

notion1 : {A : Set} → ∀ (x y : Nat) → Bool 
notion1 x y  = if not (x == y) then (x < y) or (y < x) 
-- Problem : Not really true, ask Superdock 