
-- tstp2agda proof

open import Data.FOL.Deep 3 public
open import Data.FOL.Deep.ATP.Metis 3 public

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

r : Prop
r = Var (# 2)

-- Axioms
a₁ : Prop
a₁ = (p ⇒ (q ⇒ r))


a₂ : Prop
a₂ = (p ⇒ q)


-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2

-- Conjecture
goal : Prop
goal = (p ⇒ r)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (p ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
      atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ ¬ q) ∨ r)
        weaken (atp-neg subgoal₀) $
          (assume {Γ = ∅} a1)

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
      ∧-proj₂ $ -- (p ≟ p)
        atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
          atp-strip $  -- Γ ⊢ (p ⇒ r)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
              atp-neg subgoal₁

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
          ∧-proj₂ $ -- (p ≟ p)
            atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
              atp-strip $  -- Γ ⊢ (p ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
                  atp-neg subgoal₂
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
          atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ ¬ q) ∨ r)
            weaken (atp-neg subgoal₂) $
              (assume {Γ = ∅} a1)
      )

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p q : Set} → ¬ p ∨ q)
      atp-canonicalize $  -- Γ ⊢ (¬ p ∨ q)
        weaken (atp-neg subgoal₃) $
          (assume {Γ = ∅} a2)

proof₄ : Γ ⊢ subgoal₄
proof₄ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
          ∧-proj₂ $ -- (p ≟ p)
            atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
              atp-strip $  -- Γ ⊢ (p ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
                  atp-neg subgoal₄
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p q : Set} → ¬ p ∨ q)
          atp-canonicalize $  -- Γ ⊢ (¬ p ∨ q)
            weaken (atp-neg subgoal₄) $
              (assume {Γ = ∅} a2)
      )

proof₅ : Γ ⊢ subgoal₅
proof₅ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
              ∧-proj₂ $ -- (p ≟ p)
                atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
                  atp-strip $  -- Γ ⊢ (p ⇒ r)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
                      atp-neg subgoal₅
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q : Set} → ¬ p ∨ q)
              atp-canonicalize $  -- Γ ⊢ (¬ p ∨ q)
                weaken (atp-neg subgoal₅) $
                  (assume {Γ = ∅} a2)
          )
      )
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
              ∧-proj₂ $ -- (p ≟ p)
                atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
                  atp-strip $  -- Γ ⊢ (p ⇒ r)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
                      atp-neg subgoal₅
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
              atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ ¬ q) ∨ r)
                weaken (atp-neg subgoal₅) $
                  (assume {Γ = ∅} a1)
          )
      )

proof₆ : Γ ⊢ subgoal₆
proof₆ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ r : Set} → ¬ r)
      ∧-proj₁ $ -- 5: ¬ r
        atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
          atp-strip $  -- Γ ⊢ (p ⇒ r)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
              atp-neg subgoal₆

proof₇ : Γ ⊢ subgoal₇
proof₇ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
                  ∧-proj₂ $ -- (p ≟ p)
                    atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
                      atp-strip $  -- Γ ⊢ (p ⇒ r)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
                          atp-neg subgoal₇
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q : Set} → ¬ p ∨ q)
                  atp-canonicalize $  -- Γ ⊢ (¬ p ∨ q)
                    weaken (atp-neg subgoal₇) $
                      (assume {Γ = ∅} a2)
              )
          )
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
                  ∧-proj₂ $ -- (p ≟ p)
                    atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
                      atp-strip $  -- Γ ⊢ (p ⇒ r)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
                          atp-neg subgoal₇
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ p q r : Set} → ¬ p ∨ ¬ q ∨ r)
                  atp-canonicalize $  -- Γ ⊢ ((¬ p ∨ ¬ q) ∨ r)
                    weaken (atp-neg subgoal₇) $
                      (assume {Γ = ∅} a1)
              )
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ r : Set} → ¬ r)
          ∧-proj₁ $ -- 5: ¬ r
            atp-canonicalize $  -- Γ ⊢ (¬ r ∧ p)
              atp-strip $  -- Γ ⊢ (p ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (p ⇒ r)
                  atp-neg subgoal₇
      )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

