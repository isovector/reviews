{-# OPTIONS --rewriting #-}

module RingSolving where

open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality.Rewrite
open import Function
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)


module _ (A : Set) where
  infixr 5 _+H_
  infixr 6 _*H_

  infixr 5 _:+_
  infixr 6 _:*_

  infixr 5 _+A_
  infixr 6 _*A_

  postulate
    #0 : A
    #1 : A
    _+A_ : A → A → A
    _*A_ : A → A → A

  data Poly : ℕ →  Set where
    con : A → Poly 0
    var : Poly 1
    _:+_ : {m n : ℕ} → Poly m → Poly n → Poly (m ⊔ n)
    _:*_ : {m n : ℕ} → Poly m → Poly n → Poly (m + n)


  data Horner : ℕ → Set where
    PC : A → Horner 0
    PX : {n : ℕ} → A → Horner n → Horner (suc n)

  scalMapHorner : {M : ℕ} → (A → A) → Horner M → Horner M
  scalMapHorner f (PC x) = PC (f x)
  scalMapHorner f (PX x xs) = PX (f x) (scalMapHorner f xs)

  postulate
    +A-id-l : ∀ m → #0 +A m ≡ m
    *A-id-l : ∀ m → #1 *A m ≡ m
    +A-id-r : ∀ m → m +A #0 ≡ m
    *A-id-r : ∀ m → m *A #1 ≡ m
    +A-assoc : ∀ m n p → (m +A n) +A p ≡ m +A n +A p
    *A-assoc : ∀ m n p → (m *A n) *A p ≡ m *A n *A p
    +A-comm : ∀ m n → m +A n ≡ n +A m
    *A-comm : ∀ m n → m *A n ≡ n *A m
    *A-+A-distrib : ∀ m n p → m *A (n +A p) ≡ m *A n +A m *A p
    *A-annhiliate-r : ∀ m → m *A #0 ≡ #0
    *A-annhiliate-l : ∀ m → #0 *A m ≡ #0

  {-# REWRITE +A-id-l *A-id-l +A-id-r *A-id-r *A-annhiliate-r *A-annhiliate-l +A-assoc *A-assoc *A-+A-distrib #-}

  _+H_ : {M N : ℕ} → Horner M → Horner N → Horner (M ⊔ N)
  _+H_ (PC x) (PC y) = PC (x +A y)
  _+H_ (PC x) (PX y ys) = PX (x +A y) ys
  _+H_ (PX x xs) (PC y) = PX (x +A y) xs
  _+H_ (PX x xs) (PX y ys) = PX (x +A y) (_+H_ xs ys)

  is-lt : (m : ℕ) → (n : ℕ) → n ⊔ (m Data.Nat.+ suc n) ≡ m Data.Nat.+ suc n
  is-lt m n = m≤n⇒m⊔n≡n $
    begin
      n                    ≤⟨ n≤1+n n ⟩
      suc n                ≤⟨ m≤n+m (suc n) m ⟩
      m Data.Nat.+ suc n
    ∎
    where open ≤-Reasoning

  _*H_ : {M N : ℕ} → Horner M → Horner N → Horner (M Data.Nat.+ N)
  _*H_ (PC x) y = scalMapHorner (x *A_) y
  _*H_ (PX {m} x xs) (PC y) rewrite +-identityʳ m = scalMapHorner (_*A y) (PX x xs)
  _*H_ (PX {m} x xs) yy@(PX {n} y ys) rewrite sym (is-lt m n) =
    _+H_ (scalMapHorner (x *A_) yy) (PX #0 (_*H_ xs yy))

  evaluate : {N : ℕ} → Horner N → A → A
  evaluate (PC x) v = x
  evaluate (PX x xs) v = x +A (v *A evaluate xs v)

  varH : Horner 1
  varH = PX #0 $ PC #1

  conH : A → Horner 0
  conH = PC

  construct : {N : ℕ} → Poly N → A → A
  construct (con x) a = x
  construct var a = a
  construct (p :+ p2) a = construct p a +A construct p2 a
  construct (p :* p2) a = construct p a *A construct p2 a

  toHorner : {N : ℕ} → Poly N → Horner N
  toHorner (con x) = conH x
  toHorner var = varH
  toHorner (x :+ y) = toHorner x +H toHorner y
  toHorner (x :* y) = toHorner x *H toHorner y

  test-a : Poly 2
  test-a = (var :+ con #1) :* (var :+ con #1)

  test-b : Poly 2
  test-b = var :* var :+ two :* var :+ con #1
    where
      two = con #1 :+ con #1

  swap : ∀ m n j k → (m +A n) +A (j +A k) ≡ (m +A j) +A (n +A k)
  swap m n j k =
    begin
      (m +A n) +A (j +A k)  ≡⟨ +A-assoc m n (j +A k) ⟩
      m +A (n +A (j +A k))  ≡⟨ cong (m +A_) $ sym $ +A-assoc n j k ⟩
      m +A ((n +A j) +A k)  ≡⟨ cong (\ φ → m +A (φ +A k)) $ +A-comm n j ⟩
      m +A ((j +A n) +A k)  ≡⟨ cong (m +A_) $ +A-assoc j n k ⟩
      m +A (j +A (n +A k))  ≡⟨ sym $ +A-assoc m j (n +A k) ⟩
      (m +A j) +A (n +A k)
    ∎
    where open Eq.≡-Reasoning

  swap2-*A : ∀ m n p → m *A (n *A p) ≡ n *A (m *A p)
  swap2-*A m n p  =
    begin
      m *A (n *A p)
    ≡⟨ *A-assoc m n p ⟩
      (m *A n) *A p
    ≡⟨ cong ( _*A p) $ *A-comm m n ⟩
      (n *A m) *A p
    ≡⟨ sym $ *A-assoc n m p ⟩
      n *A (m *A p)
    ∎
    where open Eq.≡-Reasoning

  +A-+H-homo : ∀ {m n} j k a → evaluate {m} j a +A evaluate {n} k a ≡ evaluate (j +H k) a
  +A-+H-homo (PC x) (PC x₁) a = refl
  +A-+H-homo (PC x) (PX x₁ k) a = refl
  +A-+H-homo (PX x x₁) (PC x₂) a =
    begin
      x +A ((a *A evaluate x₁ a) +A x₂)
    ≡⟨ cong (x +A_) $ +A-comm (a *A evaluate x₁ a) x₂ ⟩
      x +A (x₂ +A (a *A evaluate x₁ a))
    ∎
    where open Eq.≡-Reasoning
  +A-+H-homo (PX x x₁) (PX x₂ y) a rewrite +A-+H-homo x₁ y a =
    begin
      (x +A (a *A evaluate x₁ a)) +A (x₂ +A (a *A evaluate y a))  ≡⟨ swap x (a *A evaluate x₁ a) x₂ (a *A evaluate y a) ⟩
      (x +A x₂) +A ((a *A evaluate x₁ a) +A (a *A evaluate y a))  ≡⟨ cong (\φ → (x +A x₂) +A φ) (sym $ *A-+A-distrib a (evaluate x₁ a) (evaluate y a)) ⟩
      (x +A x₂) +A (a *A (evaluate x₁ a +A evaluate y a))         ≡⟨ cong (\φ → (x +A x₂) +A (a *A φ)) (+A-+H-homo x₁ y a) ⟩
      (x +A x₂) +A (a *A evaluate (x₁ +H y) a)
    ∎
    where open Eq.≡-Reasoning

  scale-evaluate : ∀ {n} x k a → x *A evaluate {n} k a ≡ evaluate {n} (scalMapHorner (x *A_) k) a
  scale-evaluate x (PC x₁) a = refl
  scale-evaluate x (PX x₁ k) a =
    begin
      x *A evaluate (PX x₁ k) a                                 ≡⟨⟩
      x *A (x₁ +A (a *A evaluate k a))                          ≡⟨ *A-+A-distrib x x₁ (a *A evaluate k a) ⟩
      (x *A x₁) +A (x *A (a *A evaluate k a))                   ≡⟨ cong ((x *A x₁) +A_) $ swap2-*A x a $ evaluate k a ⟩
      (x *A x₁) +A (a *A (x *A evaluate k a))                   ≡⟨ cong (\ φ → (x *A x₁) +A (a *A φ)) $ scale-evaluate x k a ⟩
      (x *A x₁) +A (a *A evaluate (scalMapHorner (x *A_) k) a)  ≡⟨⟩
      evaluate (PX (x *A x₁) (scalMapHorner (x *A_) k)) a       ≡⟨⟩
      evaluate (scalMapHorner (x *A_) (PX x₁ k)) a
    ∎
    where open Eq.≡-Reasoning


  *A-*H-homo : ∀ {m n} j k a → evaluate {m} j a *A evaluate {n} k a ≡ evaluate (j *H k) a
  *A-*H-homo (PC x) (PC x₁) a = refl
  *A-*H-homo (PC x) (PX x₁ k) a = cong (\ φ → (x *A x₁) +A φ) $
    begin
      x *A (a *A evaluate k a)
    ≡⟨ swap2-*A x a $ evaluate k a ⟩
      a *A (x *A evaluate k a)
    ≡⟨ cong (a *A_) $ scale-evaluate x k a ⟩
      a *A evaluate (scalMapHorner (x *A_) k) a
    ∎
    where open Eq.≡-Reasoning
  *A-*H-homo (PX x j) (PC x₁) a = ?
    -- begin
    --   (x +A a *A evaluate j a) *A x₁
    -- ≡⟨ ? ⟩
    --   evaluate (scalMapHorner (x₁ *A_) (PX x j)) a
    -- ≡⟨⟩
    --   evaluate (PX x j *H PC x₁) a
    -- ∎
    -- where open Eq.≡-Reasoning
  *A-*H-homo (PX x j) (PX x₁ k) a = ?

  isoToConstruction : {N : ℕ} → (x : Poly N) → (a : A) → construct x a ≡ evaluate (toHorner x) a
  isoToConstruction (con x) a = refl
  isoToConstruction var a = refl
  isoToConstruction (x :+ y) a
    rewrite isoToConstruction x a
          | isoToConstruction y a
          | +A-+H-homo (toHorner x) (toHorner y) a
          = refl
  isoToConstruction (x :* y) a
    rewrite isoToConstruction x a
          | isoToConstruction y a
          | *A-*H-homo (toHorner x) (toHorner y) a
          = refl

  solve : {N : ℕ} → (x y : Poly N) → toHorner x ≡ toHorner y → (a : A) → construct x a ≡ construct y a
  solve x y eq a =
    begin
      construct x a
    ≡⟨ isoToConstruction x a ⟩
      evaluate (toHorner x) a
    ≡⟨ cong (\φ → evaluate φ a) eq ⟩
      evaluate (toHorner y) a
    ≡⟨ sym $ isoToConstruction y a ⟩
      construct y a
    ∎
    where open Eq.≡-Reasoning

  blah : (x : A) → (x +A #1) *A (x +A #1) ≡ (x *A x) +A (#1 +A #1) *A x +A #1
  blah x = solve test-a test-b refl x

