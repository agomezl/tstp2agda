open import Data.Nat using (ℕ)

module Data.FOL.Deep.Theorems (n : ℕ) where

open import Data.FOL.Deep.Syntax n
open import Function using (_$_)

-- Equivalences.

postulate id : ∀ {Γ : Ctxt} {φ} → Γ ⊢ φ → Γ ⊢ φ

postulate ¬-⊤ : ∀ {Γ : Ctxt} → Γ ⊢ ¬ ⊤ → Γ ⊢ ⊥
postulate ¬-⊤₂ : ∀ {Γ : Ctxt} → Γ ⊢ ⊤ → Γ ⊢ ¬ ⊥

postulate ¬-⊥ : ∀ {Γ : Ctxt} → Γ ⊢ ¬ ⊥ → Γ ⊢ ⊤
postulate ¬-⊥₂ : ∀ {Γ : Ctxt} → Γ ⊢ ⊥ → Γ ⊢ ¬ ⊤


∧-comm  : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ φ ∧ ψ → Γ ⊢ ψ ∧ φ
∧-comm {Γ} {φ}{ψ} seq = ∧-intro (∧-proj₂ seq) (∧-proj₁ seq)

postulate ∨-equiv : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ φ ∨ ψ → Γ ⊢ ¬ (¬ φ ∧ ¬ ψ)
postulate ∨-comm  : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ φ ∨ ψ → Γ ⊢ ψ ∨ φ

postulate ¬-equiv : ∀ {Γ : Ctxt} {φ} → Γ ⊢ ¬ φ → Γ ⊢ φ ⇒ ⊥

-- Distribute Laws.
postulate ∧-dist₁ : ∀ {Γ : Ctxt} {φ ψ σ} → Γ ⊢ (φ ∨ ψ) ∧ σ → Γ ⊢ (φ ∧ σ) ∨ (ψ ∧ σ)
postulate ∧-dist₂ : ∀ {Γ : Ctxt} {φ ψ σ} → Γ ⊢ (φ ∧ σ) ∨ (ψ ∧ σ) → Γ ⊢ (φ ∨ ψ) ∧ σ

postulate ∨-dist₁ : ∀ {Γ : Ctxt} {φ ψ σ} → Γ ⊢ (φ ∧ ψ) ∨ σ → Γ ⊢ (φ ∨ σ) ∧ (ψ ∨ σ)
postulate ∨-dist₂ : ∀ {Γ : Ctxt} {φ ψ σ} → Γ ⊢ (φ ∨ σ) ∧ (ψ ∨ σ) → Γ ⊢ (φ ∧ ψ) ∨ σ

-- An example using a proof of x ∈ Γ
swap : ∀ {Γ : Ctxt} {φ ψ γ} → (Γ , φ , ψ) ⊢ γ → Γ , ψ , φ ⊢ ψ
swap {Γ} {φ = φ}{ψ} x =
  axiom {Γ = (Γ , ψ , φ)} ψ $
    there {Γ = Γ , ψ} φ $
      here {φ = ψ} {Γ = Γ}

-- van Dalen 4th Edition. Chapter 2. Section 2.4.
-- Theorem 2.4.4

th244a : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ φ ⇒ (ψ ⇒ φ)
th244a {Γ}{φ}{ψ = ψ} =
  ⇒-intro $
    ⇒-intro $
      weaken {φ = φ} ψ $
        assume {Γ = Γ} φ

th244b : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ φ ⇒ (¬ φ ⇒ ψ)
th244b {Γ}{φ = φ}{ψ = ψ} =
  ⇒-intro $
    ⇒-intro $
      ⊥-elim {Γ = (Γ , φ , ¬ φ)} ψ $
        ¬-elim
          (assume  {Γ = (Γ , φ)} (¬ φ))
          (weaken (¬ φ) (assume {Γ = Γ} φ))

th244c : ∀ {Γ : Ctxt} {φ ψ σ} → Γ ⊢ (φ ⇒ ψ) ⇒ ((ψ ⇒ σ) ⇒ (φ ⇒ σ))
th244c {Γ}{φ = φ}{ψ}{σ} =
  ⇒-intro $
     ⇒-intro $
       ⇒-intro $
         ⇒-elim {Γ = Γ , φ ⇒ ψ , ψ ⇒ σ , φ}
           (weaken φ $
             assume {Γ = Γ , φ ⇒ ψ} $ ψ ⇒ σ)
           (⇒-elim {Γ = Γ , φ ⇒ ψ , ψ ⇒ σ , φ}
             (weaken φ $
               weaken (ψ ⇒ σ) $
                 assume {Γ = Γ} $ φ ⇒ ψ)
             (assume {Γ = Γ , φ ⇒ ψ , ψ ⇒ σ} φ))

th244d : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ (¬ ψ ⇒ ¬ φ) ⇒ (φ ⇒ ψ)
th244d {Γ} {φ = φ}{ψ} =
  ⇒-intro $
    ⇒-intro $
      RAA $
        ¬-elim {Γ = Γ , ¬ ψ ⇒ ¬ φ , φ , ¬ ψ}
          (⇒-elim
            (weaken (¬ ψ) $
              weaken φ $
                assume {Γ = Γ} $ ¬ ψ  ⇒ ¬ φ)
            (assume {Γ = Γ , ¬ ψ ⇒ ¬ φ , φ} $ ¬ ψ))
          (weaken (¬ ψ) $
            assume {Γ = Γ , ¬ ψ ⇒ ¬ φ} φ)

th244e : ∀ {Γ : Ctxt} {φ} → Γ ⊢ ¬ (¬ φ) ⇒ φ
th244e {Γ} {φ} =
  ⇒-intro $ RAA
    (¬-elim {Γ = Γ , ¬ (¬ φ) , ¬ φ}
      (weaken (¬ φ) $
        assume {Γ = Γ} $ ¬ (¬ φ))
      (assume {Γ = Γ , ¬ (¬ φ)} $ ¬ φ))

e245b : ∀ {Γ Δ : Ctxt} {φ ψ} → Γ ⊢ φ → Δ , φ ⊢ ψ → Γ ⨆ Δ ⊢ ψ
e245b {Γ}{Δ = Δ} seq₁ seq₂ =
  ⇒-elim
    (weaken-Δ₂ Γ (⇒-intro seq₂))
    (weaken-Δ₁ Δ seq₁)


eComm⋀₁ : ∀ {Γ : Ctxt}{φ ψ : Prop} → Γ ⊢ φ ∧ ψ ⇒ ψ ∧ φ
eComm⋀₁ {Γ} {φ = φ}{ψ} =
  ⇒-intro $
    ∧-intro
      (∧-proj₂ $ assume {Γ = Γ} $ φ ∧ ψ)
      (∧-proj₁ {ψ = ψ} $ assume {Γ = Γ} $ φ ∧ ψ)

--- De Morgan's Law

∧-morgan₁ : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ ¬ (φ ∧ ψ) ⇒ (¬ φ ∨ ¬ ψ)
∧-morgan₁ {Γ} {φ}{ψ} =
  ⇒-intro {Γ = Γ} $
    RAA {Γ = Γ , ¬ (φ ∧ ψ)} {φ = ¬ φ ∨ ¬ ψ} $
      ¬-elim {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)}
        (weaken (¬ (¬ φ ∨ ¬ ψ)) $
          assume {Γ = Γ} $ ¬ (φ ∧ ψ))
        (∧-intro
          (RAA {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} {φ = φ}
            (¬-elim {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ) , ¬ φ}
              (weaken (¬ φ) $
                assume {Γ = Γ , ¬ (φ ∧ ψ)} $ ¬ (¬ φ ∨ ¬ ψ))
              (∨-intro₁
                (¬ ψ)
                (assume {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} $ ¬ φ))))
          (RAA {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} {φ = ψ}
            (¬-elim {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ) , ¬ ψ}
              (weaken (¬ ψ) $
                assume {Γ = Γ , ¬ (φ ∧ ψ)} $ ¬ (¬ φ ∨ ¬ ψ))
              (∨-intro₂
                (¬ φ)
                (assume {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} $ ¬ ψ )))))

postulate ∧-morgan₂ : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ ¬ φ ∨ ¬ ψ → Γ ⊢ ¬ (φ ∧ ψ)

postulate ∨-morgan₁ : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ ¬ (φ ∨ ψ) ⇒ ¬ φ ∧ ¬ ψ
postulate ∨-morgan₂ : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ ¬ φ ∧ ¬ ψ → Γ ⊢ ¬ (φ ∨ ψ)


-- auxiliar lemmas
lem1 : ∀ {Γ} {φ ψ} → Γ ⊢ ¬ ¬ φ ∨ ¬ ¬ ψ → Γ ⊢ φ ∨ ψ
lem1 {Γ} {φ}{ψ} seq =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁
          ψ
          (⇒-elim th244e $ assume {Γ = Γ} $ ¬ ¬ φ))
        (∨-intro₂
          φ
          (⇒-elim th244e $ assume {Γ = Γ} $ ¬ ¬ ψ))))
    seq

---
lem2 : ∀ {Γ} {φ ψ} → Γ ⊢ (φ ∨ ψ) ∧ ¬ ψ  → Γ ⊢ φ
lem2 {Γ} {φ}{ψ} seq =
  ⇒-elim
    (
    ⇒-intro $
      (∨-elim {Γ = Γ}
        (assume {Γ = Γ} φ)
        (⊥-elim {Γ = Γ , ψ}
          φ
          (¬-elim {Γ = Γ , ψ}
            (weaken ψ (∧-proj₂ seq))
            (assume {Γ = Γ} ψ))))
     )
    (
     ∧-proj₁ seq
    )


postulate impl-pos : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ φ ⇒ ψ → Γ ⊢  ¬ φ ∨ ψ
postulate impl-neg : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ ¬ (φ ⇒ ψ) → Γ ⊢ φ ∧ ¬ ψ

-- Translation of Formulas to Negation Normal Form.

postulate contra : ∀ {Γ : Ctxt} {φ} → Γ ⊢ φ ∧ ¬ φ → Γ ⊢ ⊥
postulate contra₂ : ∀ {Γ : Ctxt} {φ} → Γ ⊢ ¬ φ ∧ φ → Γ ⊢ ⊥

{-
mutual
  positive : Prop → Prop
  positive (Var x) = Var x
  positive ⊤ = ⊤
  positive ⊥ = ⊥
  positive (¬ φ)   = negative φ
  positive (φ ∧ ψ) = (positive φ) ∧ (positive ψ)
  positive (φ ∨ ψ) = (positive φ) ∨ (positive ψ)
  positive (φ ⇒ ψ) = (negative φ) ∨ (positive ψ)
  positive (φ ⇔ ψ) = (positive (φ ⇒ ψ)) ∧ (positive (ψ ⇒ φ))

  negative : Prop → Prop
  negative (Var x) = ¬ (Var x)
  negative ⊤ = ⊥
  negative ⊥ = ⊤
  negative (¬ φ)   = positive φ
  negative (φ ∧ ψ) = (negative φ) ∨ (negative ψ)
  negative (φ ∨ ψ) = (negative φ) ∧ (negative ψ)
  negative (φ ⇒ ψ) = (positive φ) ∧ (negative ψ)
  negative (φ ⇔ ψ) = (negative (φ ⇒ ψ)) ∨ (negative (ψ ⇒ φ))
-}


⇔-free : Prop → Prop
⇔-free (¬ φ)    = ¬ (⇔-free φ)
⇔-free (φ ∧ ψ)  = ⇔-free φ ∧ ⇔-free ψ
⇔-free (φ ∨ ψ)  = ⇔-free φ ∨ ⇔-free ψ
⇔-free (φ ⇒ ψ)  = ⇔-free φ ⇒ ⇔-free ψ
⇔-free (φ ⇔ ψ) = (φ₁ ⇒ ψ₁) ∧ (ψ₁ ⇒ φ₁)
  where
    φ₁ : Prop
    ψ₁ : Prop
    φ₁ = ⇔-free φ
    ψ₁ = ⇔-free ψ
⇔-free φ = φ

⇒-free : Prop → Prop
⇒-free (¬ φ) = ¬ ⇒-free φ
⇒-free (φ ∧ ψ) = ⇒-free φ ∧ ⇒-free ψ
⇒-free (φ ∨ ψ) = ⇒-free φ ∨ ⇒-free ψ
⇒-free (φ ⇒ ψ) = (¬ ⇒-free φ) ∨ ⇒-free ψ
⇒-free (φ ⇔ ψ) = ⇒-free φ ⇔ ⇒-free ψ
⇒-free φ = φ

-- input φ: a logic formula without implication
-- output: φ': only propositional atoms in φ' are negated and φ'≡ φ
nnf : Prop → Prop
nnf (¬ (¬ φ)) = nnf φ
nnf (φ ∧ ψ) = (nnf φ) ∧ (nnf ψ)
nnf (φ ∨ ψ) = (nnf φ) ∨ (nnf ψ)
nnf (¬ (φ ∧ ψ)) = (nnf (¬ φ)) ∨ (nnf (¬ ψ))
nnf (¬ (φ ∨ ψ)) = (nnf (¬ φ)) ∧ (nnf (¬ ψ))
nnf φ = φ

-- input η₁ η₂ : η₁, η₂ are in CNF
-- output φ': φ' is in CNF and φ' ≡ η₁ ∨ η₂
distr : Prop → Prop → Prop
distr (φ ∧ ψ) σ = (distr φ σ) ∧ (distr ψ σ)
distr φ (ψ ∨ σ) = (distr φ ψ) ∧ (distr φ σ)
distr φ ψ = φ ∨ ψ

-- input φ: an NNF formula without implication
-- output φ': φ' is in CNF and φ'≡φ
cnf : Prop → Prop
cnf (φ ∧ ψ) = (cnf φ) ∧ (cnf ψ)
cnf (φ ∨ ψ) = (cnf φ) ∨ (cnf ψ)
cnf φ = φ

clausify : Prop → Prop
clausify φ = cnf $ nnf $ ⇒-free $ ⇔-free φ
