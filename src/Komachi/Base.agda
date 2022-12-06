-- Symbolic and Automatic Differentiation of Languages, Conal Elliott
-- http://conal.net/papers/language-derivatives/
module Komachi.Base (Token : Set) where

open import Function.Base using (_∘_; flip)
open import Data.Bool
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; proj₁; proj₂; uncurry)

private variable
  A B : Set

record Parser (A : Set) : Set

record Parser A where
  coinductive
  field
    ⌊_⌋ : Maybe A
    δ : Token → Parser A

open Parser public

⌈_⌉ : Maybe A → Parser A
∅ : Parser A
ε : Parser ⊤

⌊ ⌈ y ⌉ ⌋ = y
δ ⌈ y ⌉ _ = ∅

∅ = ⌈ nothing ⌉
ε = ⌈ just tt ⌉

map : (A → B) → Parser A → Parser B
⌊ map f R ⌋ = Maybe.map f ⌊ R ⌋
δ (map f R) c = map f (δ R c)

_◁_ : Maybe A → Parser B → Parser (A × B)
nothing ◁ R = ∅
just x ◁ R = map (x ,_) R

symbol : (Token → Maybe A) → Parser A
⌊ symbol f ⌋ = nothing
δ (symbol f) x = ⌈ f x ⌉

token : (Token → Bool) → Parser ⊤
token f = symbol λ x → if f x then just tt else nothing

infixl 3 _<∣>_

_<∣>_ : Parser A → Parser A → Parser A
⌊ R <∣> S ⌋ = ⌊ R ⌋ Maybe.<∣> ⌊ S ⌋
δ (R <∣> S) c = δ R c <∣> δ S c

[_<∣>_·_] : Parser (A × B) → Parser A → Parser B → Parser (A × B)
⌊ [ R <∣> S · T ] ⌋ = ⌊ R ⌋ Maybe.<∣> Maybe.zip ⌊ S ⌋ ⌊ T ⌋
δ [ R <∣> S · T ] x = [ (δ R x <∣> ⌊ S ⌋ ◁ δ T x) <∣> δ S x · T ]

_·_ : Parser A → Parser B → Parser (A × B)
⌊ R · S ⌋ = Maybe.zip ⌊ R ⌋ ⌊ S ⌋
δ (R · S) x = [ ⌊ R ⌋ ◁ δ S x <∣> δ R x · S ]

private
  Snoc = List

[_·_★] : Parser (Snoc A) → Parser A → Parser (List A)
⌊ [ R · S ★] ⌋ = Maybe.map List.reverse ⌊ R ⌋
δ [ R · S ★] x = [ δ R x <∣> (⌊ R ⌋ ∷◁ δ S x) · S ★]
  where
    snoc : Snoc A × A → Snoc A
    snoc = uncurry (flip _∷_)

    _∷◁_ : Maybe (Snoc A) → Parser A → Parser (Snoc A)
    r ∷◁ S = map snoc (r ◁ S)

_★ : Parser A → Parser (List A)
⌊ R ★ ⌋ = just []
δ (R ★) x = [ map (_∷ []) (δ R x) · R ★]

parse : Parser A → List Token → Maybe A
parse R [] = ⌊ R ⌋
parse R (x ∷ xs) = parse (δ R x) xs
