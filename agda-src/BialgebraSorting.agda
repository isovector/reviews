{-# OPTIONS --type-in-type #-}

module BialgebraSorting where

import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function
open import Data.Product using (Σ; _,_; proj₁; proj₂)

record Functor (F : Set → Set) : Set where
  field
    map  : {A B : Set} → (A → B) → F A → F B
    map-∘ : {A B C : Set} {f : A → B} {g : B → C} → map g ∘ map f ≡ map (g ∘ f)
    map-id : {A : Set} → map (id {A = A}) ≡ id

postulate
  extensionality : {S : Set}{T : S -> Set}
                  {f g : (x : S) -> T x} ->
                  ((x : S) -> f x ≡ g x) ->
                  f ≡ g

record InitialAlgebra {F : Set → Set} (F-Functor : Functor F) : Set where
  open Functor F-Functor
  field
    Mu : Set
    In : F Mu → Mu
    inᵒ : Mu → F Mu
    In-inᵒ : In ∘ inᵒ ≡ id
    inᵒ-In : inᵒ ∘ In ≡ id
    fold
        : {A : Set} (f : F A → A)
        → Mu
        → A
    fold-∘
        : {A : Set} (f : F A → A)
        → (x : F Mu)
        → fold f (In x) ≡ f (map (fold f) x)
    fold-unique
        : {A : Set} {f : F A → A}
        → (h : Mu → A)
        → ((y : F Mu) → h (In y) ≡ f (map h y))
        → (x : Mu)
        → h x ≡ fold f x

record TerminalCoalgebra {F : Set → Set} (F-Functor : Functor F) : Set where
  open Functor F-Functor
  field
    Nu : Set
    Out : Nu → F Nu
    outᵒ : F Nu → Nu
    Out-outᵒ : Out ∘ outᵒ ≡ id
    outᵒ-Out : outᵒ ∘ Out ≡ id
    unfold : {A : Set} → (A → F A) → A → Nu
    unfold-∘
        : {A : Set} (f : A → F A)
        → (x : A)
        → Out (unfold f x) ≡ map (unfold f) (f x)
    unfold-unique
        : {A : Set} {f : A → F A}
        → (h : A → Nu)
        → ((y : A) → Out (unfold f y) ≡ map (unfold f) (f y))
        → (x : A)
        → h x ≡ unfold f x

module Example {F : Set → Set} {F-Functor : Functor F} (alg : InitialAlgebra F-Functor) where
  open Functor F-Functor
  open InitialAlgebra alg

  {-# TERMINATING #-}
  in-is-in
      : inᵒ ≡ fold (map In)
  in-is-in = extensionality $ \ x →
    let f = map In in
    begin
      inᵒ x
    ≡⟨⟩
      id (inᵒ x)
    ≡⟨ cong (_$ inᵒ x) $ sym map-id ⟩
      map id (inᵒ x)
    ≡⟨ cong (\p → map p (inᵒ x)) $ sym In-inᵒ ⟩
      map (In ∘ inᵒ) (inᵒ x)
    ≡⟨ cong (_$ inᵒ x) $ sym map-∘ ⟩
      map In (map inᵒ (inᵒ x))
    ≡⟨ cong (\p → map In ((map p) (inᵒ x))) in-is-in ⟩
      map In (map (fold (map In)) (inᵒ x))
    ≡⟨⟩
      map In (map (fold f) (inᵒ x))
    ≡⟨⟩
      f (map (fold f) (inᵒ x))
    ≡⟨ sym $ fold-∘ f (inᵒ x) ⟩
      fold f (In (inᵒ x))
    ≡⟨ cong (\p → fold f (p x)) In-inᵒ ⟩
      fold f x
    ≡⟨⟩
      fold (map In) x
    ∎

module Paper
    {F : Set → Set}
    {F-Functor : Functor F}
    (alg : InitialAlgebra F-Functor)
    (coalg : TerminalCoalgebra F-Functor) where
  open Functor F-Functor public
  open InitialAlgebra alg public
  open TerminalCoalgebra coalg public

  {-# TERMINATING #-}
  downcast : Nu → Mu
  downcast = In ∘ map downcast ∘ Out

  upcast : Mu → Nu
  upcast = fold outᵒ

data List (A : Set) (K : Set) : Set where
  Nil : List A K
  Cons : A → K → List A K

data Ordering : Set where
  LT : Ordering
  EQ : Ordering
  GT : Ordering

record Ord (A : Set) : Set where
  field
    compare : A → A → Ordering

data Bool : Set where
  false : Bool
  true  : Bool

_&&_ : Bool → Bool → Bool
false && _ = false
true && b = b

not : Bool → Bool
not false = true
not true = false

_==_ : Ordering → Ordering → Bool
_==_ EQ EQ = true
_==_ LT LT = true
_==_ GT GT = true
_==_ _ _ = false

_!=_ : Ordering → Ordering → Bool
_!=_ a b = not (a == b)

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

module Paper₂
    {A : Set}
    (Ord-A : Ord A)
    (List-Functor : Functor (List A))
    (alg : InitialAlgebra List-Functor)
    (coalg : TerminalCoalgebra List-Functor) where
  open Paper alg coalg
  open Ord Ord-A public

  is-sorted : Nu → Bool
  is-sorted = proj₂ ∘ fold (\ { Nil → nothing , true
                              ; (Cons a (nothing , x)) → just a , x
                              ; (Cons a (just a' , x)) → just a' , (x && (compare a a' != GT))
                              } ) ∘ downcast

  -- SortedList : {A : Set} → Ord A → Set
  -- SortedList ord = Σ Nu is-sorted

open Functor

record Bialgebra
       {F G : Set → Set}
       {F-functor : Functor F}
       {G-functor : Functor G}
       (f : {X : Set} → F (G X) → G (F X)) : Set where
  field
    a : {X : Set} → F X → X
    c : {X : Set} → X → G X
    bialgebra-proof
      : {X : Set}
      → c {X} ∘ a ≡ map G-functor a ∘ f ∘ map F-functor c

bubbleSort : Bialgebra ?
bubbleSort = ?

