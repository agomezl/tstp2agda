module Data.FOL.Base where

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

⊥-elim : { A : Set } → ⊥ → A
⊥-elim ()

infixl 5 _∧_ _∨_

data _∧_ ( A B : Set ) : Set where
  _,_ : A → B → A ∧ B

∧-proj₁ : ∀ {A B} → A ∧ B → A
∧-proj₁ (a , _) = a

∧-proj₂ : ∀ {A B} → A ∧ B → B
∧-proj₂ (_ , b) = b

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

case : ∀ {A B} → {C : Set} → (A → C) → (B → C) → A ∨ B → C
case f _ (inj₁ a) = f a
case _ g (inj₂ b) = g b

¬_ : Set → Set
¬ A = A → ⊥

postulate pem : ∀ {A} → A ∨ ¬ A
postulate D : Set

data ∃ ( A : D → Set ) : Set where
  _,_ : (t : D) → A t → ∃ A

∃-elim : { A : D → Set } {B : Set} → ∃ A → (∀ {x} → A x → B) → B
∃-elim (_ , Ax) h = h Ax

data _≡_ (x : D) : D → Set  where
  refl : x ≡ x



open import Function using (id)
-- postulate strip : {A : Set} → A → A
strip-0 = id
-- subgoal_0 : (z : D)
-- subgoal_0 = strip a4

proofByContradiction : {Z : Set} → (¬ Z → ⊥) → Z
proofByContradiction {Z} contradiction = case' pem
  where
    case' : Z ∨ ¬ Z → Z
    case' (inj₁ z)  = z
    case' (inj₂ nz) = ⊥-elim (contradiction nz)



-- negate_0_0 : {z : D}(~ z)
-- negate_0_0 = negate subgoal_0


canonicalize-0 = id
-- normalize_0_0 : {z : D}(~ z)
-- normalize_0_0  = canonicalize negate_0_0

postulate canonicalize-1 : { A B Z : Set } → (A ∧ B → Z) → ¬ A ∨ ¬ B ∨ Z
-- normalize_0_1 :  { A B Z : D } (~ a | ~ b | z)
-- normalize_0_1(~ a | ~ b | z) = canonicalize a3

canonicalize-2 = id
-- normalize_0_2 : (a : D)
-- normalize_0_2 = canonicalize a1

canonicalize-3 = id
-- normalize_0_3 : (b : D)
-- normalize_0_3 = canonicalize a2

postulate simplify-0 : { A B Z : Set } → A → B → ¬ A ∨ ¬ B ∨ Z → Z
-- normalize_0_4 : (z : D)
-- normalize_0_4 = simplify normalize_0_1 normalize_0_2 normalize_0_3

simplify-1 :{Z : Set} →  ¬ Z → Z → ⊥
simplify-1 f z = f z
-- normalize_0_5 : ⊥
-- normalize_0_5 = simplify normalize_0_0 normalize_0_4

canonicalize-4 = id
-- refute_0_0 : ⊥
-- refute_0_0 = canonicalize normalize_0_5

-- conclude_0 : z
--

proof : { A B Z : Set } → A → B → ( A ∧ B → Z ) → Z
proof {_}{_}{Z} a1 a2 a3 = conclude-0
  where
    normalize-0-3 = canonicalize-3 a2
    normalize-0-2 = canonicalize-2 a1
    normalize-0-1 = canonicalize-1 a3
    normalize-0-4 = simplify-0 normalize-0-2 normalize-0-3 normalize-0-1
    negate-0 : ¬ Z → ⊥
    negate-0 negatate-0-0 = refute-0-0
      where
        normalize-0-0 = id negatate-0-0
        normalize-0-5 = simplify-1 normalize-0-0 normalize-0-4
        refute-0-0 = canonicalize-4 normalize-0-5
    conclude-0 = proofByContradiction negate-0
