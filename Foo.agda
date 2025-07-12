{-# OPTIONS --polarity #-}

module Foo where

open import Data.Product

data Unit : Set where
  tt : Unit

data Nat : Set where
   z : Nat
   s : Nat -> Nat

sub : Nat -> Nat
sub z = z
sub (s x) = x

Nega : Set -> Set
Nega x = x -> Unit

Pos : Set -> Set
Pos x = Unit -> x

data U : Nat -> Nat -> Set where

data Giga : Nat -> Set where
   mkG : (n : Nat) -> Giga n -> Giga n

data GigaBad : Nat -> Set where
   mkG : (n : Nat) -> (Pos (GigaBad n × Unit) -> Unit) -> GigaBad n

data GigaBadFixed : Nat -> Set where
     mkG : (n : Nat) -> (r : Nat) -> (Pos (Nega (Nega (Nega (GigaBadFixed n)))) -> Unit) -> (k : Nat) → (U r k) -> GigaBadFixed n

data GigaBadGood : Nat -> Set where
   mkG : (n : Nat) -> (r : Nat) -> (fr : GigaBadGood n -> Unit) -> GigaBadGood (s n)

f : Unit -> Unit -> Unit
f tt x = f x tt

data Para (F : @++ Set → Set) : Set where
  mkPara : (F (Para F)) → Para F

data Zara (F : Set → Set) : Set where
  mkPara : (F (Zara F)) → Zara F

data Uara (F : @- Set → Set) : Set where
  mkPara : (F (Nega (Uara F))) → Uara F

postulate
  F : @++ Set → Set

data Mara : Set where
  mkPara : (F Mara) → Mara

data Ty : Set where
  ι : Ty
  _⇒_ : Ty → Ty → Ty

data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Ty → Ctx

variable
  Γ : Ctx
  τ τ₁ τ₂ : Ty

data Ref : Ctx → Ty → Set where
  here : Ref (Γ , τ) τ
  there : Ref Γ τ₁ → Ref (Γ , τ₂) τ₁

data HOAS : Ctx → Ty → Set where
  varr : Ref Γ τ → HOAS Γ τ
  app : HOAS Γ (τ₁ ⇒ τ₂) → HOAS Γ τ₁ → HOAS Γ τ₂
  lam : (HOAS Γ τ₁ → HOAS Γ τ₂) → HOAS Γ (τ₁ ⇒ τ₂)
