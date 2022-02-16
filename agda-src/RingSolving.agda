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
    extensionality : {S : Set}{T : S -> Set}
                    {f g : (x : S) -> T x} ->
                    ((x : S) -> f x ≡ g x) ->
                    f ≡ g

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

  normalize : {N : ℕ} → Poly N → Horner N
  normalize (con x) = conH x
  normalize var = varH
  normalize (x :+ y) = normalize x +H normalize y
  normalize (x :* y) = normalize x *H normalize y

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

  swap2-+A : ∀ m n p → m +A (n +A p) ≡ n +A (m +A p)
  swap2-+A m n p =
    begin
      m +A (n +A p)  ≡⟨ +A-assoc m n p ⟩
      (m +A n) +A p  ≡⟨ cong ( _+A p) $ +A-comm m n ⟩
      (n +A m) +A p  ≡⟨ sym $ +A-assoc n m p ⟩
      n +A (m +A p)
    ∎
    where open Eq.≡-Reasoning

  swap2-*A : ∀ m n p → m *A (n *A p) ≡ n *A (m *A p)
  swap2-*A m n p  =
    begin
      m *A (n *A p)  ≡⟨ *A-assoc m n p ⟩
      (m *A n) *A p  ≡⟨ cong ( _*A p) $ *A-comm m n ⟩
      (n *A m) *A p  ≡⟨ sym $ *A-assoc n m p ⟩
      n *A (m *A p)
    ∎
    where open Eq.≡-Reasoning

  +A-+H-homo : ∀ {m n} j k a → evaluate {m} j a +A evaluate {n} k a ≡ evaluate (j +H k) a
  +A-+H-homo (PC x) (PC x₁) a = refl
  +A-+H-homo (PC x) (PX x₁ k) a = refl
  +A-+H-homo (PX x x₁) (PC x₂) a =
    begin
      x +A ((a *A evaluate x₁ a) +A x₂)  ≡⟨ cong (x +A_) $ +A-comm (a *A evaluate x₁ a) x₂ ⟩
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
      x *A (a *A evaluate k a)  ≡⟨ swap2-*A x a $ evaluate k a ⟩
      a *A (x *A evaluate k a)  ≡⟨ cong (a *A_) $ scale-evaluate x k a ⟩
      a *A evaluate (scalMapHorner (x *A_) k) a
    ∎
    where open Eq.≡-Reasoning
  *A-*H-homo (PX {m} x j) (PC x₁) a rewrite +-identityʳ m =
    begin
      (x +A a *A evaluate j a) *A x₁                             ≡⟨ *A-comm (x +A (a *A evaluate j a)) x₁ ⟩
      x₁ *A (x +A (a *A evaluate j a))                           ≡⟨ *A-+A-distrib x₁ x (a *A evaluate j a) ⟩
      (x₁ *A x) +A (x₁ *A (a *A evaluate j a))                   ≡⟨ cong (\ φ → (x₁ *A x) +A φ) $ swap2-*A x₁ a $ evaluate j a ⟩
      (x₁ *A x) +A (a *A (x₁ *A evaluate j a))                   ≡⟨ cong (\ φ → (x₁ *A x) +A (a *A φ)) $ scale-evaluate x₁ j a ⟩
      (x₁ *A x) +A (a *A evaluate (scalMapHorner (x₁ *A_) j) a)  ≡⟨ cong (\ φ → φ +A (a *A evaluate (scalMapHorner (x₁ *A_) j) a) ) $ *A-comm x₁ x ⟩
      (x *A x₁) +A (a *A evaluate (scalMapHorner (x₁ *A_) j) a)  ≡⟨ cong (\ φ → (x *A x₁) +A (a *A evaluate (scalMapHorner φ j) a)) $ extensionality (\z → *A-comm x₁ z) ⟩
      (x *A x₁) +A (a *A evaluate (scalMapHorner (_*A x₁) j) a)
    ∎
    where open Eq.≡-Reasoning
  *A-*H-homo (PX {m} x j) (PX {n} x₁ k) a rewrite sym (is-lt m n) =
    begin
      ((x +A (a *A ej)) *A x₁) +A rhs    ≡⟨ cong (_+A rhs) $ *A-comm (x +A (a *A ej)) y ⟩
      (y *A (x +A (a *A ej))) +A rhs     ≡⟨ cong (_+A rhs) $ *A-+A-distrib y x (a *A ej) ⟩
      (y *A x +A y *A (a *A ej)) +A rhs  ≡⟨ cong (\ φ → (φ +A y *A (a *A ej)) +A rhs) $ *A-comm y x ⟩
      (xtx +A y *A (a *A ej)) +A rhs     ≡⟨ cong (\ φ → (xtx +A φ) +A rhs) $ swap2-*A y a ej ⟩
      (xtx +A a *A (y *A ej)) +A rhs     ≡⟨ +A-assoc xtx (a *A (y *A ej)) rhs ⟩
      xtx +A (a *A (y *A ej) +A rhs)     ≡⟨ cong (xtx +A_) remainder ⟩
      xtx +A (a *A evaluate (hk +H jhk) a)
    ∎
    where
      open Eq.≡-Reasoning
      ej = evaluate j a
      ek = evaluate k a
      hk = scalMapHorner (x *A_) k
      jhk = j *H PX x₁ k
      xtx = x *A x₁
      y = x₁
      rhs = ((x +A (a *A ej)) *A (a *A ek))
      xka = x *A evaluate k a

      more : (x +A (a *A ej)) *A (a *A ek) ≡ a *A ((x *A ek) +A (ej *A (a *A ek)))
      more =
        let lhs = x +A a *A ej
            cng = cong (a *A_)
            cng' = cong (\ φ → a *A ((x *A ek) +A φ))
        in
        begin
          lhs *A (a *A ek)                     ≡⟨ cong (lhs *A_) $ *A-comm a ek ⟩
          lhs *A (ek *A a)                     ≡⟨ *A-assoc lhs ek a ⟩
          (lhs *A ek) *A a                     ≡⟨ *A-comm (lhs *A ek) a ⟩
          a *A (lhs *A ek)                     ≡⟨ cng $ *A-comm lhs ek ⟩
          a *A (ek *A lhs)                     ≡⟨⟩
          a *A (ek *A (x +A a *A ej))          ≡⟨ cng $ *A-+A-distrib ek x (a *A ej) ⟩
          a *A ((ek *A x) +A ek *A (a *A ej))  ≡⟨ cng $ cong (\ φ → φ +A ek *A (a *A ej)) $ *A-comm ek x ⟩
          a *A ((x *A ek) +A ek *A (a *A ej))  ≡⟨ cng' $ cong (ek *A_) $ *A-comm a ej ⟩
          a *A ((x *A ek) +A ek *A (ej *A a))  ≡⟨ cng' $ swap2-*A ek ej a ⟩
          a *A ((x *A ek) +A ej *A (ek *A a))  ≡⟨ cng' $ cong (ej *A_) $ *A-comm ek a ⟩
          a *A ((x *A ek) +A ej *A (a *A ek))
        ∎

      owch : ∀ {m n} j k → evaluate (_*H_ {m} {n} j k) a ≡ evaluate (_*H_ {n} {m} k j) a
      owch (PC x) (PC x₁) = *A-comm x x₁
      owch (PC x) (PX {n} x₁ k) rewrite +-identityʳ n =
        begin
          x *A x₁ +A a *A evaluate (scalMapHorner (x *A_) k) a  ≡⟨ cong (\ φ → φ +A a *A evaluate (scalMapHorner (x *A_) k) a) $ *A-comm x x₁ ⟩
          x₁ *A x +A a *A evaluate (scalMapHorner (x *A_) k) a  ≡⟨ cong (\ φ → x₁ *A x +A a *A evaluate (scalMapHorner φ k) a) $ extensionality (\z → *A-comm x z) ⟩
          x₁ *A x +A a *A evaluate (scalMapHorner (_*A x) k) a
        ∎
      owch (PX {m} x j) (PC x₁) rewrite +-identityʳ m =
        begin
          x *A x₁ +A a *A evaluate (scalMapHorner (_*A x₁) j) a  ≡⟨ cong (\ φ → φ +A a *A evaluate (scalMapHorner (_*A x₁) j) a) $ *A-comm x x₁ ⟩
          x₁ *A x +A a *A evaluate (scalMapHorner (_*A x₁) j) a  ≡⟨ cong (\ φ → x₁ *A x +A a *A evaluate (scalMapHorner φ j) a) $ extensionality (\z → *A-comm z x₁) ⟩
          x₁ *A x +A a *A evaluate (scalMapHorner (x₁ *A_ ) j) a
        ∎
      owch (PX {m} x j) (PX {n} x₁ k) rewrite sym $ is-lt m n =
        begin
          evaluate (PX x j *H PX x₁ k) a
        ≡⟨ ? ⟩
          evaluate (PX x₁ k *H PX x j) a
        ∎

      remainder : a *A (y *A ej) +A rhs ≡ a *A evaluate (hk +H jhk) a
      remainder =
        begin
          (a *A (y *A ej)) +A rhs                                       ≡⟨⟩
          (a *A (y *A ej)) +A ((x +A (a *A ej)) *A (a *A ek))           ≡⟨ cong (\ φ → (a *A (y *A ej)) +A φ) more ⟩
          (a *A (y *A ej)) +A (a *A ((x *A ek) +A (ej *A (a *A ek))))   ≡⟨ sym $ *A-+A-distrib a (y *A ej) ((x *A ek) +A (ej *A (a *A ek))) ⟩
          a *A ((y *A ej) +A ((x *A ek) +A (ej *A (a *A ek))))          ≡⟨ cng $ swap2-+A (y *A ej) (x *A ek) (ej *A (a *A ek))⟩
          a *A ((x *A ek) +A ((y *A ej) +A (ej *A (a *A ek))))          ≡⟨ cng' $ cong (\ φ → (φ +A (ej *A (a *A ek)))) $ *A-comm y ej ⟩
          a *A ((x *A ek) +A ((ej *A y) +A (ej *A (a *A ek))))          ≡⟨ cng' $ sym $ *A-+A-distrib ej y (a *A ek) ⟩
          a *A ((x *A ek) +A (ej *A (y +A (a *A ek))))                  ≡⟨ cng' $ *A-comm ej (y +A (a *A ek)) ⟩
          a *A ((x *A ek) +A ((y +A (a *A ek)) *A ej))                  ≡⟨⟩
          a *A (xka +A ((x₁ +A (a *A ek)) *A ej))                       ≡⟨⟩
          a *A (xka +A ((x₁ +A (a *A evaluate k a)) *A ej))             ≡⟨⟩
          a *A (xka +A (evaluate (PX x₁ k) a *A ej))                    ≡⟨⟩
          a *A (xka +A (evaluate (PX x₁ k) a *A evaluate j a))          ≡⟨ cong (\ φ → a *A (xka +A φ)) $ *A-*H-homo (PX x₁ k) j a ⟩
          a *A (xka +A evaluate (PX x₁ k *H j) a)                       ≡⟨ cng' $ owch (PX x₁ k) j ⟩
          a *A (xka +A evaluate (j *H PX x₁ k) a)                       ≡⟨⟩
          a *A (xka +A evaluate jhk a)                                  ≡⟨⟩
          a *A ((x *A evaluate k a) +A evaluate jhk a)                  ≡⟨ cng $ cong (_+A evaluate jhk a) $ scale-evaluate x k a ⟩
          a *A (evaluate (scalMapHorner (x *A_) k) a +A evaluate jhk a) ≡⟨⟩
          a *A (evaluate hk a +A evaluate jhk a)                        ≡⟨ cng $ +A-+H-homo hk jhk a ⟩
          a *A evaluate (hk +H jhk) a
        ∎
        where
          cng = cong (a *A_)
          cng' = cong (\ φ → a *A (xka +A φ))

  isoToConstruction : {N : ℕ} → (x : Poly N) → (a : A) → construct x a ≡ evaluate (normalize x) a
  isoToConstruction (con x) a = refl
  isoToConstruction var a = refl
  isoToConstruction (x :+ y) a
    rewrite isoToConstruction x a
          | isoToConstruction y a
          | +A-+H-homo (normalize x) (normalize y) a
          = refl
  isoToConstruction (x :* y) a
    rewrite isoToConstruction x a
          | isoToConstruction y a
          | *A-*H-homo (normalize x) (normalize y) a
          = refl

  solve : {N : ℕ} → (x y : Poly N) → normalize x ≡ normalize y → (a : A) → construct x a ≡ construct y a
  solve x y eq a =
    begin
      construct x a            ≡⟨ isoToConstruction x a ⟩
      evaluate (normalize x) a  ≡⟨ cong (\φ → evaluate φ a) eq ⟩
      evaluate (normalize y) a  ≡⟨ sym $ isoToConstruction y a ⟩
      construct y a
    ∎
    where open Eq.≡-Reasoning

  test-a : Poly 2
  test-a = (var :+ con #1) :* (var :+ con #1)

  test-b : Poly 2
  test-b = var :* var :+ two :* var :+ con #1
    where
      two = con #1 :+ con #1

  blah : (x : A) → (x +A #1) *A (x +A #1) ≡ (x *A x) +A (#1 +A #1) *A x +A #1
  blah x = solve test-a test-b refl x

