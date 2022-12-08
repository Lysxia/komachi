-- As an abstract model of applicative parsers, we define languages as
-- relations between strings and values of arbitrary type.

{-# OPTIONS --allow-unsolved-metas #-}
module Komachi.Language (Token : Set) where

open import Level using (Level; zero)
open import Algebra.Definitions
open import Function using (_∘_; flip; _-⟨_⟩-_; _on_; case_of_; Morphism)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.NonEmpty as NE using (List⁺; _∷_)
open import Data.List.Properties
open import Data.List.Relation.Binary.Prefix.Heterogeneous as Prefix using (Prefix; []; _∷_)
open import Data.List.Relation.Binary.Lex.Core
open import Data.Product as Prod using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Reflexive; Symmetric; Transitive; Irreflexive; _Preserves₂_⟶_⟶_; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
import Relation.Binary.Reasoning.Base.Single as Reasoning

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

⇔-refl : Reflexive (_⇔_ {A})
⇔-refl xs = ↔-refl

⇔-sym : Symmetric (_⇔_ {A})
⇔-sym R⇔ xs = ↔-sym (R⇔ xs)

⇔-trans : Transitive (_⇔_ {A})
⇔-trans R⇔ S⇔ xs = ↔-trans (R⇔ xs) (S⇔ xs)


module _ where
  open ↔-Reasoning
  private
    _↔′_ = _IsRelatedTo_

  infixr 2 step-⇔

  step-⇔ : ∀ (R : Lang A) {S : Lang A} {T} {xs y} → (S ∋[ xs , y ]) ↔′ T → R ⇔ S → (R ∋[ xs , y ]) ↔′ T
  step-⇔ R {xs = xs} (relTo S↔) R⇔ = relTo (↔-trans (R⇔ xs) S↔)

  -- This notation is a bit confusing, because the actual LHS of the equation is R ∋[ xs , y ]
  syntax step-⇔ R S↔T R⇔S = R ⇔⟨ R⇔S ⟩ S↔T

module ⇔-Reasoning {A : Set} = Reasoning {A = Lang A} _⇔_ ⇔-refl ⇔-trans

∅ᴸ : Lang A
∅ᴸ ∋[ _ , _ ] = ⊥

εᴸ : Lang ⊤
εᴸ ∋[ xs , _ ] = [] ≡ xs

⌈_⌉ᴹ : Maybe A → A → Set
⌈ y′ ⌉ᴹ y = y′ ≡ just y

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

record [_∈_·ᴸ_] (xs : List Token) (R : Lang A) (S : Lang B) : Set where
  constructor [_++_by_]
  field
    prefix : Element R
    suffix : Element S
    prefix++suffix : prefix ₁ ++ suffix ₁ ≡ xs

open [_∈_·ᴸ_] public

_·ᴸ_ : Lang A → Lang B → Lang (A × B)
R ·ᴸ S ∋[ xs , y ] = Σ[ split ∈ [ xs ∈ R ·ᴸ S ] ] (prefix split ₂ , suffix split ₂) ≡ y

pattern [_++_by_and_] xs₁ xs₂ ++₁ ++₂ = ([ xs₁ ++ xs₂ by ++₁ ] , ++₂)

Least : (A → B → Set) → A → Set
Least _≤_ x = ∀ y → x ≤ y

Prefix-·ᴸ : ∀ {R : Lang A} {S : Lang B} {xs} → [ xs ∈ R ·ᴸ S ] → [ xs ∈ R ·ᴸ S ] → Set
Prefix-·ᴸ = Prefix _≡_ on (_₁ ∘ prefix)

record [_,_∈_<,>ᴸ_] (xs : List Token) (y : A × B) (R : Lang A) (S : Lang B) : Set where
  constructor <,>ᴸ-mk
  field
    split : R ·ᴸ S ∋[ xs , y ]
    shortest-split : Least Prefix-·ᴸ (proj₁ split)

_<,>ᴸ_ : Lang A → Lang B → Lang (A × B)
(R <,>ᴸ S) ∋[ xs , y ] = [ xs , y ∈ R <,>ᴸ S ]

zip-just : ∀ {A} {B} {x : A} {y : B} (r : Maybe A) (s : Maybe B) →
  Maybe.zip r s ≡ just (x , y) ↔
  r ≡ just x × s ≡ just y
zip-just nothing _ = (λ()) , (λ{ (() , _) })
zip-just (just _) nothing = (λ()) , (λ{ (_ , ()) })
zip-just (just x) (just y) = (λ{ refl → refl , refl }) , (λ{ (refl , refl) → refl })

δᴸ : Lang A → Token → Lang A
δᴸ R x ∋[ xs , y ] = R ∋[ x ∷ xs , y ]

δ-<∣>ᴸ : (R S : Lang A) → (x : Token) →
  δᴸ (R <∣>ᴸ S) x ⇔ δᴸ R x <∣>ᴸ δᴸ S x
δ-<∣>ᴸ R S x _ = ↔-refl

mapᴸ : (A → B) → Lang A → Lang B
mapᴸ f R ∋[ xs , y ] = ∃[ x ] R ∋[ xs , x ] × f x ≡ y

mapMaybeᴸ : (A → Maybe B) → Lang A → Lang B
mapMaybeᴸ f R ∋[ xs , y ] = ∃[ x ] R ∋[ xs , x ] × f x ≡ just y

_◁ᴸ_ : (A → Set) → Lang B → Lang (A × B)
(P ◁ᴸ R) ∋[ xs , (x , y) ] = P x × R ∋[ xs , y ]

⌊_⌋ᴸ : Lang A → A → Set
⌊ R ⌋ᴸ y = R ∋[ [] , y ]

<,>∋[] : ∀ (R : Lang A) (S : Lang B) {y₁ y₂} → R ∋[ [] , y₁ ] × S ∋[ [] , y₂ ] ↔ (R <,>ᴸ S) ∋[ [] , (y₁ , y₂) ]
<,>∋[] R S .to (r , s) = <,>ᴸ-mk [ ([] , _ , r) ++ ([] , _ , s) by refl and refl ] (λ _ → [])
<,>∋[] R S .from (<,>ᴸ-mk [ ([] , _ , r) ++ ([] , _ , s) by eq and refl ] shortest) = (r , s)

cons-[∈·ᴸ] : ∀ {R : Lang A} {S : Lang B} {xs} {x} → [ xs ∈ δᴸ R x ·ᴸ S ] → [ x ∷ xs ∈ R ·ᴸ S ]
cons-[∈·ᴸ] {x = x}
    [ (    xs₁ , y₁ , r) ++ (xs₂ , y₂ , s) by eq ]  -- Avoid pattern-matching here to to not get stuck
  = [ (x ∷ xs₁ , y₁ , r) ++ (xs₂ , y₂ , s) by cong (x ∷_) eq ]

δ-<,>ᴸ : (R : Lang A) → (S : Lang B) → (x : Token) →
  δᴸ (R <,>ᴸ S) x ⇔ ((⌊ R ⌋ᴸ ◁ᴸ δᴸ S x) <∣>ᴸ δᴸ R x <,>ᴸ S)

δ-<,>ᴸ R S x xs .to (<,>ᴸ-mk [ ([]       , y₁ , r) ++ (.x ∷ xs₂ , y₂ , s) by refl and refl ] shortest) = inj₁ (r , s)
δ-<,>ᴸ R S x xs .to (<,>ᴸ-mk [ (.x ∷ xs₁ , y₁ , r) ++ (     xs₂ , y₂ , s) by refl and refl ] shortest)
  = inj₂ (no-shorter , step)
  where
    -- ([] , _) cannot be a split of R <,>ᴸ S because we assumed that (x ∷ xs₁, xs₂) is the shortest split.
    no-shorter : ∀ {y₁ y₂} → R ∋[ [] , y₁ ] × S ∋[ x ∷ xs , y₂ ] → ⊥
    no-shorter (r′ , s′) = case shortest [ ([] , _ , r′) ++ (_ , _ , s′) by refl ] of λ()

    step : (δᴸ R x <,>ᴸ S) ∋[ xs₁ ++ xs₂ , (y₁ , y₂) ]
    step = <,>ᴸ-mk [ (xs₁ , y₁ , r) ++ (xs₂ , y₂ , s) by refl and refl ]
      (Prefix.tail ∘ shortest ∘ cons-[∈·ᴸ])

δ-<,>ᴸ R S x xs .from (inj₁ (r , s)) = <,>ᴸ-mk [ ([] , _ , r) ++ (x ∷ xs , _ , s) by refl and refl ] (λ _ → [])
δ-<,>ᴸ R S x xs .from (inj₂ (¬r , <,>ᴸ-mk [ (xs₁ , _ , r) ++ s@(xs₂ , _) by refl and refl ] shortest))
  = <,>ᴸ-mk [ (x ∷ xs₁ , _ , r) ++ s by refl and refl ] shortest′
  where
    shortest′ : (split′ : [ x ∷ xs₁ ++ xs₂ ∈ R ·ᴸ S ]) → Prefix _≡_ (x ∷ xs₁) (prefix split′ ₁)
    shortest′ [ ([] , _ , r′) ++ (_ , _ , s′) by refl ] = ⊥-elim (¬r (r′ , s′))
    shortest′ [ (_ ∷ xs′ , r′) ++ s′ by eq₁ ] with ∷-injective eq₁
    ... | refl , eq′ = refl ∷ shortest [ (xs′ , r′) ++ s′ by eq′ ]

_⊆_ : Lang A → Lang A → Set
R ⊆ S = ∀ xs {y} → R ∋[ xs , y ] → S ∋[ xs , y ]

⇔-⊆ : _⇔_ {A} ⇒ _⊆_
⇔-⊆ R⇔ xs = R⇔ xs .to

⇔-⊇ : _⇔_ {A} ⇒ flip _⊆_
⇔-⊇ R⇔ xs = R⇔ xs .from

[_∈_⊆-·ᴸ_] : ∀ xs → [_∈_·ᴸ_] {A} {B} xs Preserves₂ _⊆_ ⟶ _⊆_ ⟶ Morphism
[ xs ∈ R⊆ ⊆-·ᴸ S⊆ ]
    [ (xs₁ , y₁ ,        r) ++ (xs₂ , y₂ ,        s) by eq₁ ]
  = [ (xs₁ , y₁ , R⊆ xs₁ r) ++ (xs₂ , y₂ , S⊆ xs₂ s) by eq₁ ]

_⇔-<,>ᴸ_ : _<,>ᴸ_ {A} {B} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
_⇔-<,>ᴸ_ R⇔ S⇔ xs .to (<,>ᴸ-mk (split , eq₂) shortest)
  = <,>ᴸ-mk ([ xs ∈ ⇔-⊆ R⇔ ⊆-·ᴸ ⇔-⊆ S⇔ ] split , eq₂)
            (shortest ∘ [ xs ∈ ⇔-⊇ R⇔ ⊆-·ᴸ ⇔-⊇ S⇔ ])
_⇔-<,>ᴸ_ R⇔ S⇔ xs .from (<,>ᴸ-mk (split , eq₂) shortest)
  = <,>ᴸ-mk ([ xs ∈ ⇔-⊇ R⇔ ⊆-·ᴸ ⇔-⊇ S⇔ ] split , eq₂)
            (shortest ∘ [ xs ∈ ⇔-⊆ R⇔ ⊆-·ᴸ ⇔-⊆ S⇔ ])

_⇔-∪ᴸ_ : _∪ᴸ_ {A} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
(R⇔ ⇔-∪ᴸ S⇔) xs .to = Sum.map (R⇔ xs .to) (S⇔ xs .to)
(R⇔ ⇔-∪ᴸ S⇔) xs .from = Sum.map (R⇔ xs .from) (S⇔ xs .from)

_⇔--ᴸ_ : _-ᴸ_ {A} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
(R⇔ ⇔--ᴸ S⇔) xs = ↔-funext (↔-¬ S⇔ xs) ↔-× R⇔ xs

infixl 5 _⇔-<∣>ᴸ_
_⇔-<∣>ᴸ_ : _<∣>ᴸ_ {A} Preserves₂ _⇔_ ⟶ _⇔_ ⟶ _⇔_
R⇔ ⇔-<∣>ᴸ S⇔ = R⇔ ⇔-∪ᴸ (S⇔ ⇔--ᴸ R⇔)

∪ᴸ-assoc : Associative (_⇔_ {A}) _∪ᴸ_
∪ᴸ-assoc R S T xs = ⊎-assoc _ _ _

-ᴸ-distribʳ-∪ᴸ : _DistributesOverʳ_ (_⇔_ {A}) _-ᴸ_ _∪ᴸ_
-ᴸ-distribʳ-∪ᴸ R S T xs = ×-distribˡ-⊎ _ _ _

<∣>ᴸ-assoc : Associative (_⇔_ {A}) _<∣>ᴸ_
<∣>ᴸ-assoc R S T = begin
    (R <∣>ᴸ S) <∣>ᴸ T ≡⟨⟩
    (R ∪ᴸ (S -ᴸ R)) ∪ᴸ (T -ᴸ (R ∪ᴸ (S -ᴸ R))) ∼⟨ ∪ᴸ-assoc _ _ _ ⟩
    R ∪ᴸ ((S -ᴸ R) ∪ᴸ (T -ᴸ (R ∪ᴸ (S -ᴸ R))))
    ∼⟨ ⇔-refl ⇔-∪ᴸ (⇔-refl ⇔-∪ᴸ lemma) ⟩
    R ∪ᴸ ((S -ᴸ R) ∪ᴸ ((T -ᴸ S) -ᴸ R))
    ∼⟨ ⇔-refl ⇔-∪ᴸ (⇔-sym (-ᴸ-distribʳ-∪ᴸ R S (T -ᴸ S))) ⟩
    R ∪ᴸ ((S ∪ᴸ (T -ᴸ S)) -ᴸ R) ≡⟨⟩
    R <∣>ᴸ (S <∣>ᴸ T) ∎
  where
    lemma : T -ᴸ (R ∪ᴸ (S -ᴸ R)) ⇔ ((T -ᴸ S) -ᴸ R)
    lemma xs .to (v , t) = (v ∘ inj₁ , dne v , t)
      where
        dne : ∀ {P Q : A → Set} → (∀ {y} → ¬ (P y ⊎ ((∀ {y} → ¬ P y) × Q y))) → ∀ {y} → ¬ Q y 
        dne f q = f (inj₂ ((λ p → f (inj₁ p)) , q))
    lemma xs .from (¬r , ¬s , t) = Sum.[ ¬r , ¬s ∘ proj₂ ] , t

    open ⇔-Reasoning

∪ᴸ-identityˡ : LeftIdentity (_⇔_ {A}) ∅ᴸ _∪ᴸ_
∪ᴸ-identityˡ R xs .to (inj₂ y) = y
∪ᴸ-identityˡ R xs .from = inj₂

-ᴸ-identityʳ : RightIdentity (_⇔_ {A}) ∅ᴸ _-ᴸ_
-ᴸ-identityʳ R xs .to (_ , y) = y
-ᴸ-identityʳ R xs .from y = (λ()) , y

<∣>ᴸ-identityˡ : LeftIdentity (_⇔_ {A}) ∅ᴸ _<∣>ᴸ_
<∣>ᴸ-identityˡ R = begin
  ∅ᴸ <∣>ᴸ R ≡⟨⟩
  ∅ᴸ ∪ᴸ (R -ᴸ ∅ᴸ) ∼⟨ ∪ᴸ-identityˡ (R -ᴸ ∅ᴸ) ⟩
  (R -ᴸ ∅ᴸ) ∼⟨ -ᴸ-identityʳ R ⟩
  R ∎
  where
    open ⇔-Reasoning

data StrictPrefix {A : Set} : List A → List A → Set where
  []<∷ : ∀ {y ys} → StrictPrefix [] (y ∷ ys)
  ∷<∷ : ∀ {x xs ys} → StrictPrefix xs ys → StrictPrefix (x ∷ xs) (x ∷ ys)

-- StrictPrefix xs ys = ∃[ z ] ∃[ zs ] xs ++ z ∷ zs ≡ ys

StrictPrefix-irreflexive : Irreflexive _≡_ (StrictPrefix {A})
StrictPrefix-irreflexive refl (∷<∷ r) = StrictPrefix-irreflexive refl r

fromStrictPrefix : {xs ys : List A} → StrictPrefix xs ys → Prefix _≡_ xs ys
fromStrictPrefix []<∷ = []
fromStrictPrefix (∷<∷ sp) = refl ∷ fromStrictPrefix sp

Prefix-refl : {xs : List A} → Prefix _≡_ xs xs
Prefix-refl {xs = []} = []
Prefix-refl {xs = x ∷ xs} = refl ∷ Prefix-refl

PrefixLex : List (List A) → List (List A) → Set
PrefixLex = Lex ⊤ _≡_ StrictPrefix

record Element⁺ (R : Lang A) : Set where
  constructor [_,_,_]⁺
  field
    _₁⁺ : List⁺ Token

  _₁⁻ : List Token
  _₁⁻ = NE.toList _₁⁺

  field
    _₂⁺ : A
    mem : R ∋[ _₁⁻ , _₂⁺ ]

open Element⁺

record [_∈_☆ᴸ] (xs : List Token) (R : Lang A) : Set where
  constructor [concat_by_]
  field
    chunks : List (Element⁺ R)
    concat-chunks : List.concatMap _₁⁻ chunks ≡ xs

  values : List A
  values = List.map _₂⁺ chunks

open [_∈_☆ᴸ]

PrefixLex-☆ᴸ : {R : Lang A} → {xs : List Token} → (_ _ : [ xs ∈ R ☆ᴸ]) → Set
PrefixLex-☆ᴸ = PrefixLex on (List.map _₁⁻ ∘ chunks)

_☆ᴸ : Lang A → Lang (List A)
R ☆ᴸ ∋[ xs , y ] = Σ[ split ∈ [ xs ∈ R ☆ᴸ] ] values split ≡ y

pattern [concat_by_and_] xs eq₁ eq₂ = [concat xs by eq₁ ] , eq₂

-- Troubles in defining "minimality"
--
-- A first attempt was
--   shortest : Least PrefixLex-☆ᴸ (proj₁ split)
-- where
--   Least _≤_ x = ∀ {y} → x ≤ y
--
-- The problem comes in defining the embedding
--   mapᴸ (uncurry _∷_) (R <,>ᴸ R ★) ⊆ R ★
-- We first get a split `rr ∈ R · R ★` to construct a split `ss ∈ R ☆`.
--
-- Then we must prove that `ss` is less than any other split `ss′ ∈ R ☆`.
--
-- Intuitively, we would like to use the minimality of `rr`.
-- This requires us to construct, from `ss′ ∈ R ☆`, a split `rr′ ∈ R · R ★`,
-- which contains a minimal split as the `R ★` component, which
-- cannot be done constructively from an arbitrary split `ss′`.
record [_,_∈_★ᴸ] (xs : List Token) (y : List A) (R : Lang A) : Set where
  constructor ★ᴸ-mk
  field
    split : R ☆ᴸ ∋[ xs , y ]
    shortest : Least PrefixLex-☆ᴸ (proj₁ split)

open [_,_∈_★ᴸ]

_★ᴸ : Lang A → Lang (List A)
R ★ᴸ ∋[ xs , y ] = [ xs , y ∈ R ★ᴸ]

infix 4 _⇔⦅_⦆_ _⊆⦅_⦆_

_⊆⦅_⦆_ : Lang A → (A → B) → Lang B → Set
R ⊆⦅ f ⦆ S = ∀ xs {y} → R ∋[ xs , y ] → S ∋[ xs , f y ]

_⇔⦅_⦆_ : Lang A → (A ↔ B) → Lang B → Set
R ⇔⦅ f ⦆ S = R ⊆⦅ f .to ⦆ S × S ⊆⦅ f .from ⦆ R

uncons↔ : List A ↔ Maybe (A × List A)
uncons↔ .to = List.uncons
uncons↔ .from nothing = []
uncons↔ .from (just (x , xs)) = x ∷ xs

unnullable : Lang A → Lang A
unnullable R ∋[ xs , y ] = R ∋[ xs , y ] × ∃[ xs′ ] NE.toList xs′ ≡ xs

cons-☆ᴸ : ∀ {R : Lang A} (x : Element⁺ R) {xs} → [ xs ∈ R ☆ᴸ] → [ x ₁⁻ ++ xs ∈ R ☆ᴸ]
cons-☆ᴸ x [concat xs by eq ] = [concat (x ∷ xs) by cong (x ₁⁻ ++_) eq ]

unfold-★ᴸ : (R : Lang A) → R ★ᴸ ⇔ ⌈ just [] ⌉ᴸ <∣>ᴸ mapᴸ (uncurry _∷_) (unnullable R <,>ᴸ (R ★ᴸ))
unfold-★ᴸ R xs .to (★ᴸ-mk [concat [] by refl and refl ] shortest) = inj₁ (refl , refl)
unfold-★ᴸ R xs {.y ∷ ys} .to (★ᴸ-mk [concat ([ x , y , r ]⁺ ∷ xss) by refl and refl ] shortest)
  = inj₂ (non-empty , (y , ys) , <,>ᴸ-mk [ (NE.toList x , y , r , x , refl) ++ xss′ by refl and refl ] no-shorter , refl)
  where
    non-empty : ∀ {ys′} → ¬ (⌈ just [] ⌉ᴸ ∋[ xs , ys′ ])
    non-empty (() , _)

    no-shorter⁺ : (split′ : [ List.concatMap _₁⁻ xss ∈ R ☆ᴸ]) → PrefixLex-☆ᴸ [concat xss by refl ] split′
    no-shorter⁺ arg with shortest (cons-☆ᴸ [ x , y , r ]⁺ arg)
    ... | this z = ⊥-elim (StrictPrefix-irreflexive refl z)
    ... | next z zs = zs

    xss′ : Element (R ★ᴸ)
    xss′ = List.concatMap _₁⁻ xss , ys , ★ᴸ-mk [concat xss by refl and refl ] no-shorter⁺

    lemma : ∀ {xs} → [ xs ∈ unnullable R ·ᴸ R ★ᴸ ] → [ xs ∈ R ☆ᴸ]
    lemma [ (x₁ ∷ xs₁ , y₁ , r , .x₁ ∷ .xs₁ , refl) ++ (xs₂ , y₂ , ★ᴸ-mk [concat xs₂′ by eq₂ and _ ] _) by eq ] =
      [concat ([ x₁ ∷ xs₁ , y₁ , r ]⁺ ∷ xs₂′)
      by trans (cong₂ _++_ refl eq₂) eq ]

    no-shorter :
      (split : [ NE.toList x ++ List.concatMap _₁⁻ xss ∈ unnullable R ·ᴸ R ★ᴸ ]) →
      Prefix _≡_ (NE.toList x) (prefix split ₁)
    no-shorter split@([ (x₁ ∷ xs₁ , y₁ , r , .x₁ ∷ .xs₁ , refl) ++ (xs₂ , y₂ , r★) by eq ]) with shortest (lemma split)
    ... | this x≺y = fromStrictPrefix x≺y
    ... | next refl z = Prefix-refl

unfold-★ᴸ R xs .from (inj₁ (refl , refl)) = ★ᴸ-mk [concat [] by refl and refl ] no-shorter
  where
    no-shorter = λ where
      [concat [] by _ ] → base tt
      [concat (_ ∷ _) by _ ] → halt

unfold-★ᴸ R xs .from
    (inj₂ ( non-empty
          , (y , ys)
          , <,>ᴸ-mk [ (_ , y₁ , r , xs₁ , refl) ++ (xs₂ , y₂ , ★ᴸ-mk [concat xs₂′ by refl and refl ] shortest★)
                    by refl and refl ] shortest
          , refl))
  = ★ᴸ-mk [concat ([ xs₁ , y₁ , r ]⁺ ∷ xs₂′) by refl and refl ] no-shorter
  where
    no-shorter : Least PrefixLex-☆ᴸ [concat [ xs₁ , y , r ]⁺ ∷ xs₂′ by refl ]
    no-shorter [concat [ xs₁″ , y₁″ , r″ ]⁺ ∷ chunks₁ by concat-chunks₁ ]
        with shortest [ (_ , _ , r″ , _ , refl) ++ (_ , _ , ?) by {! !} ]
    ... | z = ?
