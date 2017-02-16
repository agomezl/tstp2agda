
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

-- Vars
clause : Prop
clause = Var (# 0)

lit : Prop
lit = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((lit ⇒ clause) ⇒ ((lit ∨ clause) ⇔ clause))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)


subgoal₁ : Prop
subgoal₁ = ((((lit ⇒ clause) ∧ clause) ∧ ¬ lit) ⇒ clause)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (clause ∨ lit)
            atp-canonicalize $  -- Γ ⊢ ((¬ clause ∧ (¬ lit ∨ clause)) ∧ (clause ∨ lit))
              atp-strip $  -- Γ ⊢ (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ ¬ clause
              atp-canonicalize $  -- Γ ⊢ ((¬ clause ∧ (¬ lit ∨ clause)) ∧ (clause ∨ lit))
                atp-strip $  -- Γ ⊢ (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)
                    atp-neg subgoal₀
            )
            (
            atp-simplify $  -- Γ ⊢ ¬ lit
              ∧-intro
                (
                atp-conjunct $  -- Γ ⊢ (¬ lit ∨ clause)
                  atp-canonicalize $  -- Γ ⊢ ((¬ clause ∧ (¬ lit ∨ clause)) ∧ (clause ∨ lit))
                    atp-strip $  -- Γ ⊢ (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)
                        atp-neg subgoal₀
                )
                (
                atp-conjunct $  -- Γ ⊢ ¬ clause
                  atp-canonicalize $  -- Γ ⊢ ((¬ clause ∧ (¬ lit ∨ clause)) ∧ (clause ∨ lit))
                    atp-strip $  -- Γ ⊢ (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)
                        atp-neg subgoal₀
                )
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-canonicalize $  -- Γ ⊢ ⊥
        atp-strip $  -- Γ ⊢ ((((lit ⇒ clause) ∧ clause) ∧ ¬ lit) ⇒ clause)
          assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((lit ⇒ clause) ∧ clause) ∧ ¬ lit) ⇒ clause)
            atp-neg subgoal₁

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (
    ∧-intro
      subgoal₀
      subgoal₁
    )

