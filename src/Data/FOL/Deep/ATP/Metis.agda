open import Data.Nat using (ℕ)

module Data.FOL.Deep.ATP.Metis (n : ℕ) where

open import Data.FOL.Deep.Syntax n
open import Data.FOL.Deep.Theorems n

open import Data.Fin
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; [_] ; foldl)
open import Data.Bool
  using (Bool ; if_then_else_ ; true ; false)
  renaming (_∧_ to _&&_ ; _∨_ to _||_)

open import Function using (_$_)

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Relation.Nullary.Decidable using (⌊_⌋)



$false : Prop
$false = ⊥

-- -----------------------------------------------------------------------------
-- Syntax equality

equal-f : Prop → Prop → Bool
equal-f (Var x) (Var y) = ⌊ x ≟ y ⌋
equal-f ⊥ ⊥ = true
equal-f ⊤ ⊤ = true
equal-f (¬ φ) (¬ ψ) = equal-f φ ψ
equal-f (φ₁ ∧ φ₂) (ψ₁ ∧ ψ₂) =
  (equal-f φ₁ ψ₁ && equal-f φ₂ ψ₂) || (equal-f φ₁ ψ₂ && equal-f φ₂ ψ₁)
equal-f (φ₁ ∨ φ₂) (ψ₁ ∨ ψ₂) =
  (equal-f φ₁ ψ₁ && equal-f φ₂ ψ₂) || (equal-f φ₁ ψ₂ && equal-f φ₂ ψ₁)
equal-f (φ₁ ⇒ φ₂) (ψ₁ ⇒ ψ₂) = equal-f φ₁ ψ₁ && equal-f φ₂ ψ₂
equal-f (φ₁ ⇔ φ₂) (ψ₁ ⇔ ψ₂) =
  (equal-f φ₁ ψ₁ && equal-f φ₂ ψ₂) || (equal-f φ₁ ψ₂ && equal-f φ₂ ψ₁)
equal-f φ ψ = false


-- -----------------------------------------------------------------------------
-- Based on Metis from src/Formula.sml.

-- strip of conjunctions.

listMkConj : List Prop → Prop
listMkConj [] = ⊤
listMkConj (fm ∷ fms) = foldl (_∧_) fm fms

stripConj : Prop → List Prop
stripConj ⊤ = []
stripConj fm = strip [] fm
  where
    strip : List Prop → Prop → List Prop
    strip cs (p ∧ q) = strip (cs ++ [ p ]) q
    strip cs fm = cs ++ [ fm ]

strip-∧ : Prop → Prop
strip-∧ fm = listMkConj $ stripConj fm

-- strip of disjunctions.

listMkDisj : List Prop → Prop
listMkDisj [] = ⊥
listMkDisj (fm ∷ fms) = foldl (_∨_) fm fms

stripDisj : Prop → List Prop
stripDisj ⊥ = []
stripDisj fm = strip [] fm
  where
    strip : List Prop → Prop → List Prop
    strip cs (p ∨ q) = strip (cs ++ [ p ]) q
    strip cs fm = cs ++ [ fm ]

strip-∨ : Prop → Prop
strip-∨ fm = listMkDisj $ stripDisj fm

-- strip of equivalences.

listMkEquiv : List Prop → Prop
listMkEquiv [] = ⊤
listMkEquiv (fm ∷ fms) = foldl (_⇔_) fm fms

stripEquiv : Prop → List Prop
stripEquiv ⊤ = []
stripEquiv fm = strip [] fm
  where
    strip : List Prop → Prop → List Prop
    strip cs (p ⇔ q) = strip ( cs ++ [ p ]) q
    strip cs fm = cs ++ [ fm ]

flatEquiv : Prop → List Prop
flatEquiv fm = flat [] [ fm ]
  where
    flat : List Prop → List Prop → List Prop
    flat acc [] = acc
    flat acc ((p ⇔ q) ∷ fms) = flat (p ∷ acc) (q ∷ fms)
    flat acc (⊤ ∷ fms) = flat acc fms
    flat acc (fm ∷ fms) = flat (fm ∷ acc) fms

strip-⇔ : Prop → Prop
strip-⇔ fm = listMkEquiv $ stripEquiv fm

-- split goal.

splitGoal₀ : Prop → List Prop
splitGoal₀ fm = split [] true fm
  where
    split : List Prop → Bool → Prop → List Prop
    split asms pol fm = case-split pol fm
      where
        case-split : Bool → Prop → List Prop
        -- positive splittables
        case-split true ⊤ = []
        case-split true (¬ f) = split asms false f
        case-split true (f₁ ∧ f₂) =
          (split asms true f₁) ++ (split (asms ++ [ f₁ ]) true f₂)
        case-split true (f₁ ∨ f₂) = split (asms ++ [ (¬ f₁) ]) true f₂
        case-split true (f₁ ⇒ f₂) = split (asms ++ [ f₁ ]) true f₂

        -- negative splittables
        case-split false ⊥ = []
        case-split false (¬ f) = split asms true f
        case-split false (f₁ ∧ f₂) = split (asms ++ [ f₁ ]) false f₂
        case-split false (f₁ ∨ f₂) =
          (split asms false f₁) ++ (split (asms ++ [ (¬ f₁) ]) false f₂)
        case-split false (f₁ ⇒ f₂) =
          (split asms true f₁) ++ (split (asms ++ [ (¬ f₁) ]) false f₂)
        case-split pol fm = [ addAsms asms (if pol then fm else (¬ fm)) ]
          where
            addAsms : List Prop → Prop → Prop
            addAsms [] goal = goal
            addAsms asms goal = (listMkConj asms) ⇒ goal


splitGoal : Prop → Prop
splitGoal fm = flat $ splitGoal₀ fm
  where
    flat : List Prop → Prop
    flat [] = ⊤
    flat (φ ∷ []) = φ
    flat (fm ∷ fms) = foldl (_∧_) fm fms

postulate atp-splitGoal : {Γ : Ctxt} {φ : Prop} → Γ ⊢ (splitGoal φ ⇒ φ)

-- Canonicalize inference.
canonicalize : Prop → Prop
canonicalize (φ ⇒ ψ)     = ¬ φ ∨ ψ
canonicalize (¬ (φ ⇒ ψ)) = if (equal-f φ ψ) then ⊥ else ((canonicalize φ) ∧ (canonicalize (¬ ψ)))
canonicalize (¬ ⊤)       = ⊥
canonicalize (¬ ⊥)       = ⊤
canonicalize (¬ (¬ φ))   = canonicalize φ
canonicalize φ           = φ

atp-canonicalize : ∀ {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ canonicalize φ
atp-canonicalize {Γ} {Var x}      = id
atp-canonicalize {Γ} {⊤}          = id
atp-canonicalize {Γ} {⊥}          = id
atp-canonicalize {Γ} {φ ∧ φ₁}     = id
atp-canonicalize {Γ} {φ ∨ φ₁}     = id
atp-canonicalize {Γ} {φ ⇒ φ₁}     = impl-pos
atp-canonicalize {Γ} {¬ (φ ⇒ φ₁)} = atp-step (λ _ → canonicalize (¬ (φ ⇒ φ₁)))

-- impl-neg
atp-canonicalize {Γ} {¬ ⊤}   = ¬-⊤
atp-canonicalize {Γ} {¬ ⊥}   = ¬-⊥₁
atp-canonicalize {Γ} {φ} seq = id (atp-step (λ _ → canonicalize φ) seq)

-- Negate inference.
atp-neg : Prop → Prop
atp-neg φ = ¬ φ


conjunct : Prop → Prop → Prop
conjunct (φ ∧ ψ) ω with (equal-f φ ω) | (equal-f ψ ω)
... | true  | _     = φ
... | false | true  = ψ
... | false | false = conjunct φ ω
conjunct φ ω = φ

atp-conjunct : ∀ {Γ} {φ} → (ω : Prop) → Γ ⊢ φ → Γ ⊢ conjunct φ ω
atp-conjunct {Γ} {φ ∧ ψ} ω seq with (equal-f φ ω) | (equal-f ψ ω)
... | true  | _     = ∧-proj₁ seq
... | false | true  = ∧-proj₂ seq
... | false | false = atp-conjunct {Γ = Γ} {φ = φ} ω (∧-proj₁ seq)
atp-conjunct {Γ} {Var x} ω  = id
atp-conjunct {Γ} {⊤} ω      = id
atp-conjunct {Γ} {⊥} ω      = id
atp-conjunct {Γ} {φ ∨ φ₁} ω = id
atp-conjunct {Γ} {φ ⇒ φ₁} ω = id
atp-conjunct {Γ} {φ ⇔ φ₁} ω = id
atp-conjunct {Γ} {¬ φ} ω    = id


-- Resolve theorems.

atp-resolve₀ : {Γ : Ctxt} {L C D : Prop} → Γ ⊢ L ∨ C → Γ ⊢ ¬ L ∨ D → Γ ⊢ C ∨ D
atp-resolve₀ {Γ} {L}{C}{D} seq₁ seq₂ =
  lem1 $ ⇒-elim {Γ = Γ}
    ∧-morgan₁
      (¬-intro {Γ = Γ} $
        ¬-elim {Γ = Γ , ¬ C ∧ ¬ D}
          (lem2 {Γ = Γ , ¬ C ∧ ¬ D} $
            ∧-intro
              (weaken (¬ C ∧ ¬ D) seq₂)
              (∧-proj₂ $ assume {Γ = Γ} $ ¬ C ∧ ¬ D))
          (lem2 $
            ∧-intro
              (weaken (¬ C ∧ ¬ D) seq₁)
              (∧-proj₁ $ assume {Γ = Γ} $ ¬ C ∧ ¬ D)))

atp-resolve₁ : {Γ : Ctxt} {L C D : Prop} → Γ ⊢ C ∨ L → Γ ⊢ ¬ L ∨ D → Γ ⊢ C ∨ D
atp-resolve₁ seq₁ = atp-resolve₀ (∨-comm seq₁)

atp-resolve₂ : {Γ : Ctxt} {L C D : Prop} → Γ ⊢ L ∨ C → Γ ⊢ D ∨ ¬ L → Γ ⊢ C ∨ D
atp-resolve₂ seq₁ seq₂ = atp-resolve₀ seq₁ (∨-comm seq₂)

atp-resolve₃ : {Γ : Ctxt} {L C D : Prop} → Γ ⊢ C ∨ L → Γ ⊢ D ∨ ¬ L → Γ ⊢ C ∨ D
atp-resolve₃ {Γ} {L}{C}{D} seq₁ seq₂ =  atp-resolve₀ (∨-comm seq₁) (∨-comm seq₂)


atp-resolve₄ : {Γ : Ctxt} {L C : Prop} → Γ ⊢ ¬ L ∨ C → Γ ⊢ L → Γ ⊢ C
atp-resolve₄ {Γ} {L} {C} seq₁ seq₂ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (assume {Γ = Γ} C)
        (assume {Γ = Γ} C)))
    (atp-resolve₀ {Γ = Γ} {L = L} {C = C} {D = C}
      (∨-intro₁ C seq₂)
      seq₁)

atp-resolve₅ : {Γ : Ctxt} {L C : Prop} → Γ ⊢ C ∨ ¬ L → Γ ⊢ L → Γ ⊢ C
atp-resolve₅ seq₁ = atp-resolve₄ (∨-comm seq₁)

atp-resolve₆ : {Γ : Ctxt} {L C : Prop} → Γ ⊢ C ∨ L → Γ ⊢ ¬ L → Γ ⊢ C
atp-resolve₆ {Γ} {L} {C} seq₁ seq₂ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (assume {Γ = Γ}  C)
        (assume {Γ = Γ} C)))
    (atp-resolve₀ (∨-comm seq₁) (∨-intro₁ C seq₂))

--
atp-resolve₇ : {Γ : Ctxt} {L C : Prop} → Γ ⊢ L ∨ C → Γ ⊢ ¬ L → Γ ⊢ C
atp-resolve₇ {Γ} {L} {C} seq₁ seq₂ = atp-resolve₆ (∨-comm seq₁) seq₂

atp-resolve₈ : {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ ¬ φ → Γ ⊢ ⊥
atp-resolve₈ seq₁ seq₂ = ¬-elim seq₂ seq₁

atp-resolve₉ : {Γ : Ctxt} {φ : Prop} → Γ ⊢ ¬ φ → Γ ⊢ φ → Γ ⊢ ⊥
atp-resolve₉ = ¬-elim


swap-seq : ∀ {Γ} {φ ψ} → Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ ψ → Γ ⊢ φ
swap-seq seq₁ seq₂ = λ _ → seq₁

-- Simplify inference.

isOpposite : Prop → Prop → Bool
isOpposite (¬ (¬ φ)) ψ  = isOpposite φ ψ
isOpposite φ (¬ (¬ ψ))  = isOpposite φ ψ
isOpposite φ ψ with equal-f φ (¬ ψ) | equal-f (¬ φ) ψ
isOpposite φ ψ | true  | _ = true
isOpposite φ ψ | false | y = y

simplify : Prop → Prop
simplify (Var x)  = Var x
simplify ⊤        = ⊤
simplify ⊥        = ⊥
simplify (φ ⇒ φ₁) = φ ⇒ φ₁
simplify ((φ ⇒ ψ) ∧ ω) with equal-f φ ω
... | true  = simplify ψ
... | false =  (φ ⇒ ψ) ∧ ω -- simplify ((¬ φ ∨ ψ) ∧ ω)
simplify ((φ ⇔ (ψ ⇔ ω)) ∧ ρ) with equal-f φ ρ | equal-f ψ ρ | equal-f ω ρ
... | true | _    | _     = simplify (ψ ⇔ ω)
... | _    | true | _     = simplify (φ ⇔ ω)
... | _    | _    | true  = simplify (φ ⇔ ψ)
... | _    | _    | false with equal-f (φ ⇔ ψ) ρ
...                       | true  = ω
...                       | false with equal-f (φ ⇔ ω) ρ
...                               | true  = ψ
...                               | false with equal-f (ψ ⇔ ω) ρ
...                                       | true = φ
...                                       | false = φ ⇔ (ψ ⇔ ω)
simplify (φ ⇔ φ₁) = φ ⇔ φ₁
simplify (¬ ⊥)    = ⊤
simplify (¬ ⊤)    = ⊥
simplify (⊥ ∧ φ)  = ⊥
simplify (φ ∧ ⊥)  = ⊥
simplify (⊥ ∨ φ)  = simplify φ
simplify (φ ∨ ⊥)  = simplify φ
simplify (⊤ ∧ φ)  = simplify φ
simplify (φ ∧ ⊤)  = simplify φ
simplify (φ ∧ (ψ ∨ ω)) with isOpposite φ (¬ ψ)
... | true  = simplify ω
... | false with isOpposite φ (¬ ω)
...         | true  = simplify ψ
...         | false = φ ∧ (ψ ∨ ω)
simplify ((φ ∨ ψ) ∧ ω) with isOpposite ω (¬ φ)
... | true  = simplify ψ
... | false with isOpposite ω (¬ ψ)
...         | true  = simplify φ
...         | false = (φ ∨ ψ) ∧ ω
simplify ((φ ∨ ψ) ∧ ω ∧ ρ) with isOpposite φ ω | isOpposite ψ ρ
... | true | _    = ψ ∧ ρ
... | _    | true = φ ∧ ρ
... | _    | _    = (φ ∨ ψ) ∧ ω ∧ ρ
simplify (φ ∧ ψ ∧ ω) =
  if isOpposite φ ψ || isOpposite φ ω || isOpposite ψ ω then ⊥
  else φ ∧ ψ ∧ ω
simplify (φ ∧ ψ) with equal-f φ ψ
simplify (φ ∧ ψ) | true  = simplify φ
simplify (φ ∧ ψ) | false with equal-f φ (¬ ψ) | equal-f (¬ φ) ψ
simplify (φ ∧ ψ) | false | false | false = φ ∧ ψ
simplify (φ ∧ ψ) | false | _     | _     = ⊥
simplify (φ ∨ ψ) with equal-f φ ψ
simplify (φ ∨ ψ) | true = simplify φ
simplify (φ ∨ ψ) | false with equal-f φ (¬ ψ) | equal-f (¬ φ) ψ
simplify (φ ∨ ψ) | false | false | false = φ ∨ ψ
simplify (φ ∨ ψ) | false | _     | _     = ⊤
simplify φ = φ


atp-simplify : ∀ {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ simplify φ
atp-simplify {Γ} {Var x} = id --id
atp-simplify {Γ} {⊤}     = id -- id
atp-simplify {Γ} {⊥}     = id -- id
atp-simplify {Γ} {φ = φ₁ ∧ ¬ φ₂} seq =
  atp-step (λ _ → simplify (φ₁ ∧ ¬ φ₂)) seq
atp-simplify {Γ} {¬ φ ∧ ψ} =
  atp-step (λ _ → simplify (¬ φ ∧ ψ))
atp-simplify {Γ} {φ} seq = id (atp-step (λ _ → simplify φ) seq)

-- Strip inference.
strip : Prop → Prop
strip (Var x) = (Var x)
strip (¬ ⊤)   = ⊥
strip (¬ ⊥)   = ⊤
strip (¬ φ)   = ¬ φ
strip (φ₁ ∨ φ₂ ∨ φ₃)   = (¬ φ₁) ∧ (¬ φ₂) ⇒ φ₃
strip (φ ∨ ψ)          = (¬ φ) ⇒ ψ
strip (φ₁ ⇒ (φ₂ ⇒ φ₃)) = φ₁ ∧ (strip (φ₂ ⇒ φ₃))
strip φ = φ

atp-strip : ∀ {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ strip φ
atp-strip {Γ} {Var x} = id
atp-strip {Γ} {(φ₁ ⇒ (φ₂ ⇒ φ₃))} =
  atp-step (λ _ → φ₁ ∧ strip (φ₂ ⇒ φ₃))
atp-strip {Γ} {¬ ⊤}   = ¬-⊤
atp-strip {Γ} {¬ ⊥}   = ¬-⊥₁
atp-strip {Γ} {φ} seq = id (atp-step (λ _ → strip φ) seq)


-- clausify : Prop → Prop
-- clausify x = ?
