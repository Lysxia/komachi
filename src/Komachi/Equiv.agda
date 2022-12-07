-- Logical equivalence
module Komachi.Equiv where

open import Algebra.Definitions
open import Function.Base using (_∘_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Prod using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Reflexive; Symmetric; Transitive; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
import Relation.Binary.Reasoning.Base.Single as Reasoning

infix 1 _↔_
infixr 4 _,_

-- Logical equivalence between two propositions
record _↔_ (P Q : Set) : Set where
  constructor _,_
  field
    to : P → Q
    from : Q → P

open _↔_ public

↔-refl : Reflexive _↔_
↔-refl = (λ x → x) , (λ x → x)

↔-sym : Symmetric _↔_
↔-sym (f , g) = g , f

↔-trans : Transitive _↔_
↔-trans (f₁ , f₂) (g₁ , g₂) = g₁ ∘ f₁ , f₂ ∘ g₂

module ↔-Reasoning = Reasoning {A = Set} _↔_ ↔-refl ↔-trans

_↔-⊎_ : _⊎_ Preserves₂ _↔_ ⟶ _↔_ ⟶ _↔_
(f , f′) ↔-⊎ (g , g′) = Sum.map f g , Sum.map f′ g′

_↔-×_ : _×_ Preserves₂ _↔_ ⟶ _↔_ ⟶ _↔_
(f , f′) ↔-× (g , g′) = Prod.map f g , Prod.map f′ g′

↔-funext : ∀ {A : Set} {P Q : A → Set} → (∀ {x} → P x ↔ Q x) → (∀ {x} → P x) ↔ (∀ {x} → Q x)
↔-funext f = (λ p → f .to p) , (λ p → f .from p)

↔-¬_ : ¬_ Preserves _↔_ ⟶ _↔_
↔-¬ (f , f′) = (_∘ f′ , _∘ f)

⊎-assoc : Associative _↔_ _⊎_
⊎-assoc P Q R = Sum.assocʳ , Sum.assocˡ 

×-distribˡ-⊎ : _DistributesOverˡ_ _↔_ _×_ _⊎_
×-distribˡ-⊎ P Q R .to (p , qr) = Sum.map (p ,_) (p ,_) qr
×-distribˡ-⊎ P Q R .from = Sum.[ Prod.map₂ inj₁ , Prod.map₂ inj₂ ]
