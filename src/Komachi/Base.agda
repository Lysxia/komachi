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

-- We add a way to signal that a parser is definitely empty so that we can
-- discard it and thus avoid exponential blowups.
record Parser (A : Set) : Set
Parser? : Set → Set

record Parser A where
  coinductive
  field
    ⌊_⌋ : Maybe A
    δ : Token → Parser? A

Parser? A = Maybe (Parser A)

open Parser public

infixr 4 _<,>_ _*>_ _<*_ _$>_
infixl 3 _<∣>_ _<∣>?_

∅? : Parser? A
∅? = nothing

⌈_⌉ : Maybe A → Parser A
∅ : Parser A
ε : Parser ⊤

⌊ ⌈ y ⌉ ⌋ = y
δ ⌈ y ⌉ _ = ∅?

∅ = ⌈ nothing ⌉
ε = ⌈ just tt ⌉

⌈_⌉? : Maybe A → Parser? A
⌈_⌉? = Maybe.map λ y → ⌈ just y ⌉

mapMaybe : (A → Maybe B) → Parser A → Parser B
⌊ mapMaybe f R ⌋ = ⌊ R ⌋ Maybe.>>= f
δ (mapMaybe f R) c with δ R c
... | nothing = nothing
... | just R′ = just (mapMaybe f R′)

map : (A → B) → Parser A → Parser B
map f = mapMaybe (just ∘ f)

map? : (A → B) → Parser? A → Parser? B
map? = Maybe.map ∘ map

_◁_ : Maybe A → Parser B → Parser (A × B)
nothing ◁ R = ∅
just x ◁ R = map (x ,_) R

_◁?_ : Maybe A → Parser? B → Parser? (A × B)
_◁?_ = Maybe.zipWith (_◁_ ∘ just)

symbol : (Token → Maybe A) → Parser A
⌊ symbol f ⌋ = nothing
δ (symbol f) x = ⌈ f x ⌉?

token : (Token → Bool) → Parser ⊤
token f = symbol λ x → if f x then just tt else nothing

_<∣>_ : Parser A → Parser A → Parser A
_<∣>?_ : Parser? A → Parser? A → Parser? A
⌊ R <∣> S ⌋ = ⌊ R ⌋ Maybe.<∣> ⌊ S ⌋
δ (R <∣> S) c = δ R c <∣>? δ S c

nothing <∣>? S = S
R <∣>? nothing = R
just R <∣>? just S = just (R <∣> S)

⌊_⌋? : Parser? A → Maybe A
⌊_⌋? = (Maybe._>>= ⌊_⌋)

δ? : Parser? A → Token → Parser? A
δ? R x = R Maybe.>>= λ R′ → δ R′ x

-- This notation must be read associated like this: R <∣> (S <,> T)
[_<∣>_<,>_] : Parser? (A × B) → Parser A → Parser B → Parser (A × B)
[_<∣>_?<,>_] : Parser? (A × B) → Parser? A → Parser B → Parser? (A × B)

⌊ [ R <∣> S <,> T ] ⌋ = ⌊ R ⌋? Maybe.<∣> Maybe.zip ⌊ S ⌋ ⌊ T ⌋
δ [ R <∣> S <,> T ] x = [ (δ? R x <∣>? ⌊ S ⌋ ◁? δ T x) <∣> δ S x ?<,> T ]

[ R <∣> nothing ?<,> T ] = R
[ R <∣> just S ?<,> T ] = just [ R <∣> S <,> T ]

_<,>_ : Parser A → Parser B → Parser (A × B)
_<,>_ = [ nothing <∣>_<,>_]

private
  Snoc = List

-- This notation must be read associated like this: R <,> (S ★)
[_<,>_★] : Parser (Snoc A) → Parser A → Parser (List A)
[_?<,>_★] : Parser? (Snoc A) → Parser A → Parser? (List A)

⌊ [ R <,> S ★] ⌋ = Maybe.map List.reverse ⌊ R ⌋
δ [ R <,> S ★] x = [ δ R x <∣>? (⌊ R ⌋ ∷◁? δ S x) ?<,> S ★]
  where
    snoc : Snoc A × A → Snoc A
    snoc = uncurry (flip _∷_)

    _∷◁?_ : Maybe (Snoc A) → Parser? A → Parser? (Snoc A)
    r ∷◁? S = map? snoc (r ◁? S)

[ nothing ?<,> S ★] = nothing
[ just R ?<,> S ★] = just [ R <,> S ★]

_★ : Parser A → Parser (List A)
⌊ R ★ ⌋ = just []
δ (R ★) x = [ map? (_∷ []) (δ R x) ?<,> R ★]

_*>_ : Parser A → Parser B → Parser B
R *> S = map proj₂ (R <,> S)

_<*_ : Parser A → Parser B → Parser A
R <* S = map proj₁ (R <,> S)

_$>_ : Parser A → B → Parser B
R $> x = map (λ _ → x) R

parse : Parser A → List Token → Maybe A
parse? : Parser? A → List Token → Maybe A

parse R [] = ⌊ R ⌋
parse R (x ∷ xs) = parse? (δ R x) xs

parse? nothing _ = nothing
parse? (just R) xs = parse R xs
