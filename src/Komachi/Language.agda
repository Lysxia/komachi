-- As an abstract model of applicative parsers, we define languages as
-- relations between strings and values of arbitrary type.

{-# OPTIONS --allow-unsolved-metas #-}
module Komachi.Language (Token : Set) where

open import Level using (Level; zero)
open import Function.Base using (_∘_; flip; _on_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous as Prefix using (Prefix; []; _∷_)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (REL; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Komachi.Equiv

private variable
  A B : Set

record Lang (A : Set) : Set₁ where
  infix 5 _∋[_,_]
  field
    _∋[_,_] : List Token → A → Set

open Lang public

_∈_ : List Token → Lang A → Set
xs ∈ R = ∃[ y ] R ∋[ xs , y ]

Element : Lang A → Set
Element R = ∃[ xs ] xs ∈ R

_₁ : {R : Lang A} → Element R → List Token
_₁ (xs , _) = xs

_₂ : {R : Lang A} → Element R → A
_₂ (xs , y , _) = y

_∉_ : List Token → Lang A → Set
xs ∉ R = ∀ {y} → ¬ R ∋[ xs , y ]

infix 4 _⇔_

-- Language equivalence: they relate the same elements.
-- The first argument is explicit because in proofs we almost always pattern-match on it.
_⇔_ : (R S : Lang A) → Set
R ⇔ S = ∀ x {y} → R ∋[ x , y ] ↔ S ∋[ x ,  y ]

∅ᴸ : Lang A
∅ᴸ ∋[ _ , _ ] = ⊥

εᴸ : Lang ⊤
εᴸ ∋[ xs , _ ] = [] ≡ xs

⌈_⌉ᴸ : Maybe A → Lang A
⌈ y′ ⌉ᴸ ∋[ xs , y ] = xs ≡ [] × y′ ≡ just y

pattern ⌈just⌉ᴸ∋ = refl , refl

_∪ᴸ_ : Lang A → Lang A → Lang A
(R ∪ᴸ S) ∋[ xs , y ] = R ∋[ xs , y ] ⊎ S ∋[ xs , y ]

-- Language difference
_-ᴸ_ : Lang A → Lang A → Lang A
(R -ᴸ S) ∋[ xs , y ] = xs ∉ S × R ∋[ xs , y ]

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

record [_∈_<,>ᴸ_] (xs : List Token) (R : Lang A) (S : Lang B) : Set where
  constructor [_++_by_]
  field
    prefix : Element R
    suffix : Element S
    prefix++suffix : prefix ₁ ++ suffix ₁ ≡ xs

  value : A × B
  value = prefix ₂ , suffix ₂

open [_∈_<,>ᴸ_] public

Least : (A → A → Set) → A → Set
Least _≤_ x = ∀ y → x ≤ y

_<,>ᴸ_ : Lang A → Lang B → Lang (A × B)
(R <,>ᴸ S) ∋[ xs , y ] = def R S xs y
  module <,>ᴸ where 
    record def (R : Lang A) (S : Lang B) (xs : List Token) (y : A × B) : Set where
      constructor mk
      field
        split : [ xs ∈ R <,>ᴸ S ]
        shortest-split : Least (Prefix _≡_ on (_₁ ∘ prefix)) split
        value-split : value split ≡ y

zip-just : ∀ {A} {B} {x : A} {y : B} (r : Maybe A) (s : Maybe B) →
  Maybe.zip r s ≡ just (x , y) ↔
  r ≡ just x × s ≡ just y
zip-just nothing _ = (λ()) , (λ{ (() , _) })
zip-just (just _) nothing = (λ()) , (λ{ (_ , ()) })
zip-just (just x) (just y) = (λ{ refl → refl , refl }) , (λ{ (refl , refl) → refl })

{-
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
-}

δᴸ : Lang A → Token → Lang A
δᴸ R x ∋[ xs , y ] = R ∋[ x ∷ xs , y ]

δ-<∣>ᴸ : (R S : Lang A) → (x : Token) →
  δᴸ (R <∣>ᴸ S) x ⇔ δᴸ R x <∣>ᴸ δᴸ S x
δ-<∣>ᴸ R S x _ = ↔-refl

mapᴸ : (A → B) → Lang A → Lang B
mapᴸ f R ∋[ xs , y ] = ∃[ x ] R ∋[ xs , x ] × f x ≡ y

_◁ᴸ_ : (A → Set) → Lang B → Lang (A × B)
(P ◁ᴸ R) ∋[ xs , (x , y) ] = P x × R ∋[ xs , y ]

⌊_⌋ᴸ : Lang A → A → Set
⌊ R ⌋ᴸ y = R ∋[ [] , y ]

δ-<,>ᴸ : (R : Lang A) → (S : Lang B) → (x : Token) →
  δᴸ (R <,>ᴸ S) x ⇔ ((⌊ R ⌋ᴸ ◁ᴸ δᴸ S x) <∣>ᴸ δᴸ R x <,>ᴸ S)
δ-<,>ᴸ R S x xs .to (<,>ᴸ.mk [ ([]       , y₁ , r) ++ (.x ∷ xs₂ , y₂ , s) by refl ] shortest refl) = inj₁ (r , s)
δ-<,>ᴸ R S x xs .to (<,>ᴸ.mk [ (.x ∷ xs₁ , y₁ , r) ++ (     xs₂ , y₂ , s) by refl ] shortest refl)
  = inj₂ (no-shorter , next)
  where
    no-shorter : ∀ {y₁ y₂} → R ∋[ [] , y₁ ] × S ∋[ x ∷ xs , y₂ ] → ⊥
    no-shorter = ?

    next : (δᴸ R x <,>ᴸ S) ∋[ xs₁ ++ xs₂ , (y₁ , y₂) ]
    next = <,>ᴸ.mk [ (xs₁ , y₁ , r) ++ (xs₂ , y₂ , s) by refl ] ? ?
δ-<,>ᴸ R S x xs .from = ?

_⇔-∪ᴸ_ : _∪ᴸ_ {A} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
(R⇔ ⇔-∪ᴸ S⇔) xs .to = Sum.map (R⇔ xs .to) (S⇔ xs .to)
(R⇔ ⇔-∪ᴸ S⇔) xs .from = Sum.map (R⇔ xs .from) (S⇔ xs .from)

_⇔--ᴸ_ : _-ᴸ_ {A} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
(R⇔ ⇔--ᴸ S⇔) xs = ↔-funext (↔-¬ S⇔ xs) ↔-× R⇔ xs


_⇔-<∣>ᴸ_ : _<∣>ᴸ_ {A} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
R⇔ ⇔-<∣>ᴸ S⇔ = R⇔ ⇔-∪ᴸ (S⇔ ⇔--ᴸ R⇔)
