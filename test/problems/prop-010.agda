
-- tstp2agda proof

open import Data.FOL.Deep 4 public
open import Data.FOL.Deep.ATP.Metis 4 public

-- Vars
a : Prop
a = Var (# 0)

g : Prop
g = Var (# 1)

k : Prop
k = Var (# 2)

q : Prop
q = Var (# 3)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((g ∨ (¬ a ∧ k)) ≟ (g ∨ (¬ a ∧ k)))
            atp-canonicalize $  -- Γ ⊢ (((¬ k ∧ ¬ q) ∧ (¬ g ∨ q)) ∧ (g ∨ (¬ a ∧ k)))
              atp-strip $  -- Γ ⊢ (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-simplify $  -- Γ ⊢ ¬ g
              ∧-intro
                (
                ∧-proj₁ $ -- 1: ((¬ k ∧ ¬ q) ∧ (¬ g ∨ q))
                  atp-canonicalize $  -- Γ ⊢ (((¬ k ∧ ¬ q) ∧ (¬ g ∨ q)) ∧ (g ∨ (¬ a ∧ k)))
                    atp-strip $  -- Γ ⊢ (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)
                        atp-neg subgoal₀
                )
                (
                ∧-proj₁ $ -- 1: ((¬ k ∧ ¬ q) ∧ (¬ g ∨ q))
                  atp-canonicalize $  -- Γ ⊢ (((¬ k ∧ ¬ q) ∧ (¬ g ∨ q)) ∧ (g ∨ (¬ a ∧ k)))
                    atp-strip $  -- Γ ⊢ (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)
                        atp-neg subgoal₀
                )
            )
            (
            ∧-proj₁ $ -- 1: ((¬ k ∧ ¬ q) ∧ (¬ g ∨ q))
              atp-canonicalize $  -- Γ ⊢ (((¬ k ∧ ¬ q) ∧ (¬ g ∨ q)) ∧ (g ∨ (¬ a ∧ k)))
                atp-strip $  -- Γ ⊢ (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((a ∨ ¬ k) ⇒ g) ∧ (g ⇒ q)) ∧ ¬ q) ⇒ k)
                    atp-neg subgoal₀
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

