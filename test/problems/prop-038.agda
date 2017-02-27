
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (¬ (p ⇔ q) ⇔ ((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = ((¬ (p ⇔ q) ∧ p) ⇒ ¬ q)


subgoal₁ : Prop
subgoal₁ = (((¬ (p ⇔ q) ∧ (p ⇒ ¬ q)) ∧ q) ⇒ ¬ p)


subgoal₂ : Prop
subgoal₂ = ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ p) ⇒ ¬ q)


subgoal₃ : Prop
subgoal₃ = ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ q) ⇒ ¬ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ p ⇔ q) ≟ (¬ p ⇔ q))
            atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ (¬ p ⇔ q))
              atp-strip $  -- Γ ⊢ ((¬ (p ⇔ q) ∧ p) ⇒ ¬ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((¬ (p ⇔ q) ∧ p) ⇒ ¬ q)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (p ∧ q)
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ (¬ p ⇔ q))
                atp-strip $  -- Γ ⊢ ((¬ (p ⇔ q) ∧ p) ⇒ ¬ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((¬ (p ⇔ q) ∧ p) ⇒ ¬ q)
                    atp-neg subgoal₀
            )
            (
            ∧-proj₁ $ -- 1: (p ∧ q)
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ (¬ p ⇔ q))
                atp-strip $  -- Γ ⊢ ((¬ (p ⇔ q) ∧ p) ⇒ ¬ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((¬ (p ⇔ q) ∧ p) ⇒ ¬ q)
                    atp-neg subgoal₀
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₁ $ -- 1: ((p ∧ q) ∧ (¬ p ∨ ¬ q))
            atp-canonicalize $  -- Γ ⊢ (((p ∧ q) ∧ (¬ p ∨ ¬ q)) ∧ (¬ p ⇔ q))
              atp-strip $  -- Γ ⊢ (((¬ (p ⇔ q) ∧ (p ⇒ ¬ q)) ∧ q) ⇒ ¬ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ (p ⇔ q) ∧ (p ⇒ ¬ q)) ∧ q) ⇒ ¬ p)
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((p ∧ q) ∧ (¬ p ∨ ¬ q))
              atp-canonicalize $  -- Γ ⊢ (((p ∧ q) ∧ (¬ p ∨ ¬ q)) ∧ (¬ p ⇔ q))
                atp-strip $  -- Γ ⊢ (((¬ (p ⇔ q) ∧ (p ⇒ ¬ q)) ∧ q) ⇒ ¬ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ (p ⇔ q) ∧ (p ⇒ ¬ q)) ∧ q) ⇒ ¬ p)
                    atp-neg subgoal₁
            )
            (
            ∧-proj₁ $ -- 1: ((p ∧ q) ∧ (¬ p ∨ ¬ q))
              atp-canonicalize $  -- Γ ⊢ (((p ∧ q) ∧ (¬ p ∨ ¬ q)) ∧ (¬ p ⇔ q))
                atp-strip $  -- Γ ⊢ (((¬ (p ⇔ q) ∧ (p ⇒ ¬ q)) ∧ q) ⇒ ¬ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((¬ (p ⇔ q) ∧ (p ⇒ ¬ q)) ∧ q) ⇒ ¬ p)
                    atp-neg subgoal₁
            )
          )

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ p ∨ ¬ q) ≟ (¬ p ∨ ¬ q))
            atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ (¬ p ∨ ¬ q))
              atp-strip $  -- Γ ⊢ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ p) ⇒ ¬ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ p) ⇒ ¬ q)
                  atp-neg subgoal₂
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (p ∧ q)
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ (¬ p ∨ ¬ q))
                atp-strip $  -- Γ ⊢ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ p) ⇒ ¬ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ p) ⇒ ¬ q)
                    atp-neg subgoal₂
            )
            (
            ∧-proj₁ $ -- 1: (p ∧ q)
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ (¬ p ∨ ¬ q))
                atp-strip $  -- Γ ⊢ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ p) ⇒ ¬ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ p) ⇒ ¬ q)
                    atp-neg subgoal₂
            )
          )

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ p ∨ ¬ q) ≟ (¬ p ∨ ¬ q))
            atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ (¬ p ∨ ¬ q))
              atp-strip $  -- Γ ⊢ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ q) ⇒ ¬ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ q) ⇒ ¬ p)
                  atp-neg subgoal₃
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (p ∧ q)
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ (¬ p ∨ ¬ q))
                atp-strip $  -- Γ ⊢ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ q) ⇒ ¬ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ q) ⇒ ¬ p)
                    atp-neg subgoal₃
            )
            (
            ∧-proj₁ $ -- 1: (p ∧ q)
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∧ (¬ p ∨ ¬ q))
                atp-strip $  -- Γ ⊢ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ q) ⇒ ¬ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ q) ⇒ ¬ p)
                    atp-neg subgoal₃
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (
    ∧-intro
      subgoal₀
      (
      ∧-intro
        subgoal₁
        (
        ∧-intro
          subgoal₂
          subgoal₃
        )
      )
    )

