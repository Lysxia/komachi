module Komachi.Properties (Token : Set) where

open import Function.Base using (_$_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Komachi.Equiv
open import Komachi.Language Token
open import Komachi.Base Token

private variable
  A B : Set

⟦_⟧ : Parser A → Lang A
⟦ R ⟧ ∋[ xs , y ] = parse R xs ≡ just y

⟦_⟧? : Parser? A → Lang A
⟦ R ⟧? ∋[ xs , y ] = parse? R xs ≡ just y

⟦⟧?-[] : (R : Parser? A) (y : A) → ⟦ R ⟧? ∋[ [] , y ] ↔ ⌊ R ⌋? ≡ just y
⟦⟧?-[] nothing y = ↔-refl
⟦⟧?-[] (just y′) y = ↔-refl

⟦δ_⟧ : ∀ (R : Parser A) {x} → ⟦ δ R x ⟧? ⇔ δᴸ ⟦ R ⟧ x
⟦δ R ⟧ = ⇔-refl

⟦δ?_⟧ : ∀ (R : Parser? A) {x} → ⟦ δ? R x ⟧? ⇔ δᴸ ⟦ R ⟧? x
⟦δ? nothing ⟧ xs = (λ()) , (λ())
⟦δ? just y ⟧ xs = ↔-refl

⟦∅⟧ : ⟦ ∅ ⟧ ⇔ ∅ᴸ {A}
⟦∅⟧ [] .to ()
⟦∅⟧ (x ∷ xs) .to ()
⟦∅⟧ xs .from ()

⟦ε⟧ : ⟦ ε ⟧ ⇔ εᴸ
⟦ε⟧ [] .to _ = refl
⟦ε⟧ (x ∷ xs) .to ()
⟦ε⟧ xs .from refl = refl

⟦⌈_⌉⟧ : (y : Maybe A) → ⟦ ⌈ y ⌉ ⟧ ⇔ ⌈ y ⌉ᴸ
⟦⌈ just y ⌉⟧ [] .to refl = ⌈just⌉ᴸ∋
⟦⌈ y ⌉⟧ (x ∷ xs) .to ()
⟦⌈ nothing ⌉⟧ [] .to ()
⟦⌈ (just y) ⌉⟧ xs .from ⌈just⌉ᴸ∋ = refl

⟦_<∣>_⟧⇔ : (R S : Parser A) → ⟦ R <∣> S ⟧ ⇔ ⟦ R ⟧ <∣>ᴸ ⟦ S ⟧
⟦_<∣>?_⟧⇔ : (R S : Parser? A) → ⟦ R <∣>? S ⟧? ⇔ ⟦ R ⟧? <∣>ᴸ ⟦ S ⟧?

⟦ R <∣> S ⟧⇔ [] = <∣>-just ⌊ R ⌋ ⌊ S ⌋
⟦ R <∣> S ⟧⇔ (x ∷ xs) {y} = ⟦ δ R x <∣>? δ S x ⟧⇔ xs

⟦ nothing <∣>? S ⟧⇔ xs .to S-xs-y = inj₂ ((λ()) , S-xs-y)
⟦ nothing <∣>? S ⟧⇔ xs .from (inj₂ (_ , S-xs-y)) = S-xs-y
⟦ R@(just _) <∣>? nothing ⟧⇔ xs .to R-xs-y = inj₁ R-xs-y
⟦ R@(just _) <∣>? nothing ⟧⇔ xs .from (inj₁ R-xs-y) = R-xs-y
⟦ just R <∣>? just S ⟧⇔ = ⟦ R <∣> S ⟧⇔

is-not-just-⌊_⌋? : (R : Parser? A) →
  is-not-just ⌊ R ⌋? ↔ [] ∉ ⟦ R ⟧?
is-not-just-⌊ nothing ⌋? .to _ ()
is-not-just-⌊ nothing ⌋? .from _ ()
is-not-just-⌊ just R ⌋? = ↔-refl

⟦_◁_⟧⇔ : (y : Maybe A) → (R : Parser B) →
  ⟦ y ◁ R ⟧ ⇔ (⌈ y ⌉ᴹ ◁ᴸ ⟦ R ⟧)
⟦ nothing ◁ R ⟧⇔ [] = (λ()) , λ{(() , _)}
⟦ nothing ◁ R ⟧⇔ (_ ∷ _) = (λ()) , λ{(() , _)}
⟦ just y ◁ R ⟧⇔ [] with ⌊ R ⌋
... | nothing = (λ()) , λ{(_ , ())}
... | just z = (λ{ refl → refl , refl }) , (λ{ (refl , refl) → refl })
⟦ just y ◁ R ⟧⇔ (x ∷ xs) with δ R x
... | nothing = (λ()) , λ{(_ , ())}
... | just R′ = ⟦ just y ◁ R′ ⟧⇔ xs

⟦_◁?_⟧⇔ : (y : Maybe A) → (R : Parser? B) →
  ⟦ y ◁? R ⟧? ⇔ (⌈ y ⌉ᴹ ◁ᴸ ⟦ R ⟧?)
⟦ nothing ◁? R ⟧⇔ _ = (λ()) , (λ{(() , _)})
⟦ just y ◁? nothing ⟧⇔ _ =  (λ()) , (λ{(_ , ())})
⟦ just y ◁? just R ⟧⇔ = ⟦ just y ◁ R ⟧⇔

⟦⌊_⌋◁?_⟧ : (R : Parser A) → (S : Parser? B) →
  ⟦ ⌊ R ⌋ ◁? S ⟧? ⇔ ⌊ ⟦ R ⟧ ⌋ᴸ ◁ᴸ ⟦ S ⟧?
⟦⌊ R ⌋◁? S ⟧ xs with ⌊ R ⌋ | S
... | nothing | S = (λ()) , λ{ (() , _) }
... | just _ | nothing = (λ()) , λ{ (_ , ()) }
... | just y | just S = ⟦ just y ◁ S ⟧⇔ xs

⟦[_<∣>_<,>_]⟧ : (R : Parser? (A × B)) → (S : Parser A) → (T : Parser B) →
  ⟦ [ R <∣> S <,> T ] ⟧ ⇔ ⟦ R ⟧? <∣>ᴸ (⟦ S ⟧ <,>ᴸ ⟦ T ⟧)
⟦[_<∣>_?<,>_]⟧ : (R : Parser? (A × B)) → (S : Parser? A) → (T : Parser B) →
  ⟦ [ R <∣> S ?<,> T ] ⟧? ⇔ ⟦ R ⟧? <∣>ᴸ (⟦ S ⟧? <,>ᴸ ⟦ T ⟧)

⟦[ R <∣> S <,> T ]⟧ [] {y} = begin
  (⌊ R ⌋? Maybe.<∣> Maybe.zip ⌊ S ⌋ ⌊ T ⌋ ≡ just y)
  ∼⟨ <∣>-just ⌊ R ⌋? _ ⟩
  (⌊ R ⌋? ≡ just y ⊎ is-not-just ⌊ R ⌋? × Maybe.zip ⌊ S ⌋ ⌊ T ⌋ ≡ just y)
  ∼⟨ ↔-sym (⟦⟧?-[] R y) ↔-⊎ (is-not-just-⌊ R ⌋? ↔-× (↔-trans (zip-just _ _) (<,>∋[] ⟦ S ⟧ ⟦ T ⟧))) ⟩
  ((⟦ R ⟧? <∣>ᴸ (⟦ S ⟧ <,>ᴸ ⟦ T ⟧)) ∋[ [] , y ]) ∎
  where open ↔-Reasoning

⟦[ R <∣> S <,> T ]⟧ (x ∷ xs) {y} = begin
  ⟦ [ (δ? R x <∣>? (⌊ S ⌋ ◁? δ T x)) <∣> δ S x ?<,> T ] ⟧? ∋[ xs , y ]
  ∼⟨ ⟦[ (δ? R x <∣>? (⌊ S ⌋ ◁? δ T x)) <∣> δ S x ?<,> T ]⟧ xs ⟩
  ⟦ δ? R x <∣>? (⌊ S ⌋ ◁? δ T x) ⟧? <∣>ᴸ ⟦ δ S x ⟧? <,>ᴸ ⟦ T ⟧
  ⇔⟨ ⟦ δ? R x <∣>? _ ⟧⇔ ⇔-<∣>ᴸ ⇔-refl ⟩
  ⟦ δ? R x ⟧? <∣>ᴸ ⟦ ⌊ S ⌋ ◁? δ T x ⟧? <∣>ᴸ ⟦ δ S x ⟧? <,>ᴸ ⟦ T ⟧
  ⇔⟨ <∣>ᴸ-assoc _ _ _ ⟩
  ⟦ δ? R x ⟧? <∣>ᴸ (⟦ ⌊ S ⌋ ◁? δ T x ⟧? <∣>ᴸ ⟦ δ S x ⟧? <,>ᴸ ⟦ T ⟧)
  ⇔⟨ ⇔-refl ⇔-<∣>ᴸ (⟦⌊ S ⌋◁? δ T x ⟧ ⇔-<∣>ᴸ ⇔-refl) ⟩
  ⟦ δ? R x ⟧? <∣>ᴸ ((⌊ ⟦ S ⟧ ⌋ᴸ ◁ᴸ δᴸ ⟦ T ⟧ x) <∣>ᴸ δᴸ ⟦ S ⟧ x <,>ᴸ ⟦ T ⟧)
  ⇔⟨ ⟦δ? R ⟧ ⇔-<∣>ᴸ ⇔-sym (δ-<,>ᴸ ⟦ S ⟧ ⟦ T ⟧ x) ⟩
  δᴸ ⟦ R ⟧? x <∣>ᴸ δᴸ (⟦ S ⟧ <,>ᴸ ⟦ T ⟧) x ∋[ xs , y ]
  ≡⟨⟩
  δᴸ (⟦ R ⟧? <∣>ᴸ (⟦ S ⟧ <,>ᴸ ⟦ T ⟧)) x ∋[ xs , y ] ∎
  where open ↔-Reasoning

⟦[ R <∣> nothing ?<,> T ]⟧ xs .to = inj₁
⟦[ R <∣> nothing ?<,> T ]⟧ xs .from (inj₁ eq) = eq
⟦[ R <∣> just S ?<,> T ]⟧ = ⟦[ R <∣> S <,> T ]⟧

⟦nothing⟧ : ⟦ nothing {A = Parser A} ⟧? ⇔ ∅ᴸ
⟦nothing⟧ [] = (λ()) , (λ())
⟦nothing⟧ (_ ∷ _) = (λ()) , (λ())

⟦_<,>_⟧⇔ : (R : Parser A) → (S : Parser B) →
  ⟦ R <,> S ⟧ ⇔ ⟦ R ⟧ <,>ᴸ ⟦ S ⟧
⟦ R <,> S ⟧⇔ = begin
  ⟦ [ nothing <∣> R <,> S ] ⟧ ∼⟨ ⟦[ nothing <∣> R <,> S ]⟧ ⟩
  ⟦ nothing ⟧? <∣>ᴸ ⟦ R ⟧ <,>ᴸ ⟦ S ⟧ ∼⟨ ⟦nothing⟧ ⇔-<∣>ᴸ ⇔-refl ⟩
  ∅ᴸ <∣>ᴸ ⟦ R ⟧ <,>ᴸ ⟦ S ⟧ ∼⟨ <∣>ᴸ-identityˡ _ ⟩
  ⟦ R ⟧ <,>ᴸ ⟦ S ⟧ ∎
  where open ⇔-Reasoning
