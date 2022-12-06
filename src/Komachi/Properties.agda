module Komachi.Properties (Token : Set) where

open import Function.Base using (_∘_; flip)
open import Level using (Level; zero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous as List using (Prefix; []; _∷_)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Definitions using (Reflexive; Transitive)

open import Komachi.Base Token

private variable
  A B : Set

infix 1 _<->_

record _<->_ (P Q : Set) : Set where
  constructor _,_
  field
    to : P → Q
    from : Q → P

open _<->_

Lang : Set → Set₁
Lang A = REL (List Token) A zero

infix 4 _⇔_

-- This order of arguments works better for us than the stdlib.
_⇔_ : (R S : Lang A) → Set
R ⇔ S = ∀ x {y} → R x y <-> S x y

<->-refl : Reflexive _<->_
<->-refl = (λ x → x) , (λ x → x)

<->-trans : Transitive _<->_
<->-trans f g with f | g
... | f₁ , f₂ | g₁ , g₂ = g₁ ∘ f₁ , f₂ ∘ g₂

import Relation.Binary.Reasoning.Base.Single as Reasoning
module <->-Reasoning = Reasoning {A = Set} _<->_ <->-refl <->-trans

⟦_⟧ : Parser A → Lang A
⟦ R ⟧ xs y = parse R xs ≡ just y

∅ᴿ : Lang A
∅ᴿ _ _ = ⊥

εᴿ : Lang ⊤
εᴿ xs _ = [] ≡ xs

data ⌈_⌉ᴿ {A : Set} : Maybe A → Lang A where
  ⌈just_⌉ᴿ : (y : A) → ⌈ just y ⌉ᴿ [] y

⟦∅⟧ : ⟦ ∅ ⟧ ⇔ ∅ᴿ {A}
⟦∅⟧ [] .to ()
⟦∅⟧ (x ∷ xs) .to = ⟦∅⟧ xs .to
⟦∅⟧ xs .from ()

⟦ε⟧ : ⟦ ε ⟧ ⇔ εᴿ
⟦ε⟧ [] .to _ = refl
⟦ε⟧ (x ∷ xs) .to eq = ⊥-elim (⟦∅⟧ xs .to eq)
⟦ε⟧ xs .from refl = refl

⟦⌈_⌉⟧ : (y : Maybe A) → ⟦ ⌈ y ⌉ ⟧ ⇔ ⌈ y ⌉ᴿ
⟦⌈ just y ⌉⟧ [] .to refl = ⌈just y ⌉ᴿ
⟦⌈ y ⌉⟧ (x ∷ xs) .to eq = ⊥-elim (⟦∅⟧ xs .to eq)
⟦⌈ nothing ⌉⟧ [] .to ()
⟦⌈ .(just y) ⌉⟧ xs .from ⌈just y ⌉ᴿ = refl

infixl 5 _<∣>ᴿ_
_<∣>ᴿ_ : Lang A → Lang A → Lang A
(R <∣>ᴿ S) xs y = R xs y ⊎ (∀ {y′} → ¬ R xs y′) × S xs y

-- this is _≡ nothing but with exactly the right shape for the next lemma.
is-not-just : (r : Maybe A) → Set
is-not-just r = ∀ {x} → ¬ r ≡ just x

<∣>-just : (r s : Maybe A) → {x : A} →
  ((r Maybe.<∣> s) ≡ just x) <-> (r ≡ just x ⊎ is-not-just r × s ≡ just x)
<∣>-just r s .from (inj₁ refl) = refl
<∣>-just (just x) s .to refl = inj₁ refl
<∣>-just (just _) s .from (inj₂ (¬just , _)) = ⊥-elim (¬just refl)
<∣>-just nothing s .to refl = inj₂ ((λ()) , refl)
<∣>-just nothing s .from (inj₂ (¬just , refl)) = refl

⟦_<∣>_⟧⇔ : (R S : Parser A) → ⟦ R <∣> S ⟧ ⇔ ⟦ R ⟧ <∣>ᴿ ⟦ S ⟧
⟦ R <∣> S ⟧⇔ [] = <∣>-just ⌊ R ⌋ ⌊ S ⌋
⟦ R <∣> S ⟧⇔ (x ∷ xs) = ⟦ δ R x <∣> δ S x ⟧⇔ xs

record ∃-shortest (P : List Token → Set) : Set where
  constructor ex-shortest
  field
    witness : List Token
    P-witness : P witness
    shortest : (xs : List Token) → P xs → Prefix _≡_ witness xs

open ∃-shortest

_·ᴿ_ : Lang A → Lang B → Lang (A × B)
(R ·ᴿ S) xs (y₁ , y₂) = ∃-shortest λ xs₁ → ∃[ xs₂ ] xs₁ ++ xs₂ ≡ xs × R xs₁ y₁ × S xs₂ y₂ 

⊎-cong : ∀ {P P′ Q Q′} → P <-> P′ → Q <-> Q′ → (P ⊎ Q) <-> (P′ ⊎ Q′)
⊎-cong (f , f′) (g , g′) = Sum.map f g , Sum.map f′ g′

×-cong : ∀ {P P′ Q Q′} → P <-> P′ → Q <-> Q′ → (P × Q) <-> (P′ × Q′)
×-cong (f , f′) (g , g′) = Prod.map f g , Prod.map f′ g′

zip-just : ∀ {A} {B} {x : A} {y : B} (r : Maybe A) (s : Maybe B) →
  Maybe.zip r s ≡ just (x , y) <->
  r ≡ just x × s ≡ just y
zip-just nothing _ = (λ()) , (λ{ (() , _) })
zip-just (just _) nothing = (λ()) , (λ{ (_ , ()) })
zip-just (just x) (just y) = (λ{ refl → refl , refl }) , (λ{ (refl , refl) → refl })

sigma-++-nil : {f : List Token → List Token → Set} →
  f [] [] <-> ∃-shortest λ xs₁ → ∃[ xs₂ ] xs₁ ++ xs₂ ≡ [] × f xs₁ xs₂
sigma-++-nil .to f[][] = λ where
  .witness → []
  .P-witness → [] , refl , f[][]
  .shortest → λ _ _ → []
sigma-++-nil .from =
  λ where
    (ex-shortest [] ([] , refl , eq) _) → eq
    (ex-shortest [] ((_ ∷ _) , () , eq) _)
    (ex-shortest (_ ∷ _) (xs₂ , () , eq) _)

δᴿ : Lang A → Token → Lang A
δᴿ R x xs = R (x ∷ xs)

δ-<∣>ᴿ : (R S : Lang A) → (x : Token) →
  δᴿ (R <∣>ᴿ S) x ⇔ δᴿ R x <∣>ᴿ δᴿ S x
δ-<∣>ᴿ R S x _ = <->-refl

mapᴿ : (A → B) → Lang A → Lang B
mapᴿ f R xs y = ∃[ x ] R xs x × f x ≡ y

_◁ᴿ_ : (A → Set) → Lang B → Lang (A × B)
(P ◁ᴿ R) xs (x , y) = P x × R xs y

⌊_⌋ᴿ : Lang A → A → Set
⌊ R ⌋ᴿ y = R [] y

δ-·ᴿ : (R : Lang A) → (S : Lang B) → (x : Token) →
  δᴿ (R ·ᴿ S) x ⇔ ((⌊ R ⌋ᴿ ◁ᴿ δᴿ S x) <∣>ᴿ δᴿ R x ·ᴿ S)
δ-·ᴿ R S x xs .to (ex-shortest [] (xs₂ , refl , Req , Seq) sw) = inj₁ (Req , Seq)
δ-·ᴿ R S x xs .to (ex-shortest (x ∷ xs₁) (xs₂ , refl , Req , Seq) sw) = inj₂ λ where
  .proj₁ → ?
  .proj₂ .witness → ?
  .proj₂ .P-witness → ?
  .proj₂ .shortest → ?
δ-·ᴿ R S x xs .from = ?

⟦[_<∣>_·_]⟧ : (R : Parser (A × B)) → (S : Parser A) → (T : Parser B) →
  ⟦ [ R <∣> S · T ] ⟧ ⇔ ⟦ R ⟧ <∣>ᴿ (⟦ S ⟧ ·ᴿ ⟦ T ⟧)
⟦[ R <∣> S · T ]⟧ [] {y@(y₁ , y₂)} = begin
  (⌊ R ⌋ Maybe.<∣> Maybe.zip ⌊ S ⌋ ⌊ T ⌋ ≡ just y) ∼⟨ <∣>-just ⌊ R ⌋ _ ⟩
  (⌊ R ⌋ ≡ just y ⊎ is-not-just ⌊ R ⌋ × Maybe.zip ⌊ S ⌋ ⌊ T ⌋ ≡ just y)
  ∼⟨ ⊎-cong <->-refl (×-cong <->-refl (<->-trans (zip-just _ _) sigma-++-nil)) ⟩
  ((⟦ R ⟧ <∣>ᴿ (⟦ S ⟧ ·ᴿ ⟦ T ⟧)) [] y) ∎
  where open <->-Reasoning
⟦[ R <∣> S · T ]⟧ (x ∷ xs) {y@(y₁ , y₂)} = begin
  (⟦ [ (δ R x <∣> (⌊ S ⌋ ◁ δ T x)) <∣> δ S x · T ] ⟧ xs y)
  ∼⟨ ⟦[ (δ R x <∣> (⌊ S ⌋ ◁ δ T x)) <∣> δ S x · T ]⟧ xs {y} ⟩
  _  ∼⟨ ? ⟩
  ((δᴿ ⟦ R ⟧ x <∣>ᴿ δᴿ (⟦ S ⟧ ·ᴿ ⟦ T ⟧) x) xs y) ≡⟨⟩
  (δᴿ (⟦ R ⟧ <∣>ᴿ (⟦ S ⟧ ·ᴿ ⟦ T ⟧)) x xs y) ≡⟨⟩
  ((⟦ R ⟧ <∣>ᴿ (⟦ S ⟧ ·ᴿ ⟦ T ⟧)) (x ∷ xs) y) ∎
  where open <->-Reasoning

