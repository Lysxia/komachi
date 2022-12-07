-- As an abstract model of applicative parsers, we define languages as
-- relations between strings and values of arbitrary type.

{-# OPTIONS --allow-unsolved-metas #-}
module Komachi.Language (Token : Set) where

open import Level using (Level; zero)
open import Function.Base using (_∘_; flip)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous as Prefix using (Prefix; []; _∷_)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (REL; Reflexive; Symmetric; Transitive; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  A B : Set

Lang : Set → Set₁
Lang A = REL (List Token) A zero

infix 1 _↔_

record _↔_ (P Q : Set) : Set where
  constructor _,_
  field
    to : P → Q
    from : Q → P

open _↔_ public

infix 4 _⇔_

-- Language equivalence: they relate the same elements.
-- The first argument is explicit because in proofs we almost always pattern-match on it.
_⇔_ : (R S : Lang A) → Set
R ⇔ S = ∀ x {y} → R x y ↔ S x y

↔-refl : Reflexive _↔_
↔-refl = (λ x → x) , (λ x → x)

↔-sym : Symmetric _↔_
↔-sym (f , g) = g , f

↔-trans : Transitive _↔_
↔-trans (f₁ , f₂) (g₁ , g₂) = g₁ ∘ f₁ , f₂ ∘ g₂

import Relation.Binary.Reasoning.Base.Single as Reasoning
module ↔-Reasoning = Reasoning {A = Set} _↔_ ↔-refl ↔-trans

∅ᴸ : Lang A
∅ᴸ _ _ = ⊥

εᴸ : Lang ⊤
εᴸ xs _ = [] ≡ xs

data ⌈_⌉ᴸ {A : Set} : Maybe A → Lang A where
  ⌈just_⌉ᴸ : (y : A) → ⌈ just y ⌉ᴸ [] y

_∪ᴸ_ : Lang A → Lang A → Lang A
(R ∪ᴸ S) xs y = R xs y ⊎ S xs y

-- Language difference
_-ᴸ_ : Lang A → Lang A → Lang A
(R -ᴸ S) xs y = (∀ {y′} → ¬ S xs y′) × R xs y

infixl 5 _<∣>ᴸ_
_<∣>ᴸ_ : Lang A → Lang A → Lang A
R <∣>ᴸ S = R ∪ᴸ (S -ᴸ R)

-- this is _≡ nothing but with exactly the right shape for the next lemma.
is-not-just : (r : Maybe A) → Set
is-not-just r = ∀ {x} → ¬ r ≡ just x

<∣>-just : (r s : Maybe A) → {x : A} →
  ((r Maybe.<∣> s) ≡ just x) ↔ (r ≡ just x ⊎ is-not-just r × s ≡ just x)
<∣>-just r s .from (inj₁ refl) = refl
<∣>-just (just x) s .to refl = inj₁ refl
<∣>-just (just _) s .from (inj₂ (¬just , _)) = ⊥-elim (¬just refl)
<∣>-just nothing s .to refl = inj₂ ((λ()) , refl)
<∣>-just nothing s .from (inj₂ (¬just , refl)) = refl

record ∃-shortest (P : List Token → Set) : Set where
  constructor ex-shortest
  field
    witness : List Token
    P-witness : P witness
    shortest : (xs : List Token) → P xs → Prefix _≡_ witness xs

open ∃-shortest public

_<,>ᴸ_ : Lang A → Lang B → Lang (A × B)
(R <,>ᴸ S) xs (y₁ , y₂) = ∃-shortest λ xs₁ → ∃[ xs₂ ] xs₁ ++ xs₂ ≡ xs × R xs₁ y₁ × S xs₂ y₂ 

_↔-⊎_ : ∀ {P P′ Q Q′} → P ↔ P′ → Q ↔ Q′ → (P ⊎ Q) ↔ (P′ ⊎ Q′)
(f , f′) ↔-⊎ (g , g′) = Sum.map f g , Sum.map f′ g′

_↔-×_ : ∀ {P P′ Q Q′} → P ↔ P′ → Q ↔ Q′ → (P × Q) ↔ (P′ × Q′)
(f , f′) ↔-× (g , g′) = Prod.map f g , Prod.map f′ g′

zip-just : ∀ {A} {B} {x : A} {y : B} (r : Maybe A) (s : Maybe B) →
  Maybe.zip r s ≡ just (x , y) ↔
  r ≡ just x × s ≡ just y
zip-just nothing _ = (λ()) , (λ{ (() , _) })
zip-just (just _) nothing = (λ()) , (λ{ (_ , ()) })
zip-just (just x) (just y) = (λ{ refl → refl , refl }) , (λ{ (refl , refl) → refl })

sigma-++-nil : {f : List Token → List Token → Set} →
  f [] [] ↔ ∃-shortest λ xs₁ → ∃[ xs₂ ] xs₁ ++ xs₂ ≡ [] × f xs₁ xs₂
sigma-++-nil .to f[][] = λ where
  .witness → []
  .P-witness → [] , refl , f[][]
  .shortest → λ _ _ → []
sigma-++-nil .from =
  λ where
    (ex-shortest [] ([] , refl , eq) _) → eq
    (ex-shortest [] ((_ ∷ _) , () , eq) _)
    (ex-shortest (_ ∷ _) (xs₂ , () , eq) _)

δᴸ : Lang A → Token → Lang A
δᴸ R x xs = R (x ∷ xs)

δ-<∣>ᴸ : (R S : Lang A) → (x : Token) →
  δᴸ (R <∣>ᴸ S) x ⇔ δᴸ R x <∣>ᴸ δᴸ S x
δ-<∣>ᴸ R S x _ = ↔-refl

mapᴸ : (A → B) → Lang A → Lang B
mapᴸ f R xs y = ∃[ x ] R xs x × f x ≡ y

_◁ᴸ_ : (A → Set) → Lang B → Lang (A × B)
(P ◁ᴸ R) xs (x , y) = P x × R xs y

⌊_⌋ᴸ : Lang A → A → Set
⌊ R ⌋ᴸ y = R [] y

δ-<,>ᴸ : (R : Lang A) → (S : Lang B) → (x : Token) →
  δᴸ (R <,>ᴸ S) x ⇔ ((⌊ R ⌋ᴸ ◁ᴸ δᴸ S x) <∣>ᴸ δᴸ R x <,>ᴸ S)
δ-<,>ᴸ R S x xs .to (ex-shortest [] (xs₂ , refl , Req , Seq) sw) = inj₁ (Req , Seq)
δ-<,>ᴸ R S x xs .to (ex-shortest (x ∷ xs₁) (xs₂ , refl , Req , Seq) sw) = inj₂ λ where
  .proj₁ → ?
  .proj₂ .witness → ?
  .proj₂ .P-witness → ?
  .proj₂ .shortest → ?
δ-<,>ᴸ R S x xs .from = ?

_⇔-∪ᴸ_ : _∪ᴸ_ {A} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
(R⇔ ⇔-∪ᴸ S⇔) xs .to = Sum.map (R⇔ xs .to) (S⇔ xs .to)
(R⇔ ⇔-∪ᴸ S⇔) xs .from = Sum.map (R⇔ xs .from) (S⇔ xs .from)

_⇔--ᴸ_ : _-ᴸ_ {A} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
_⇔--ᴸ_ = ?


_⇔-<∣>ᴸ_ : _<∣>ᴸ_ {A} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
R⇔ ⇔-<∣>ᴸ S⇔ = R⇔ ⇔-∪ᴸ (S⇔ ⇔--ᴸ R⇔)
