
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

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r)))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)


subgoal₁ : Prop
subgoal₁ = ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)


subgoal₂ : Prop
subgoal₂ = ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)


subgoal₃ : Prop
subgoal₃ = (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((p ∨ (q ∧ r)) ≟ (p ∨ (q ∧ r)))
            atp-canonicalize $  -- Γ ⊢ ((¬ p ∧ ¬ q) ∧ (p ∨ (q ∧ r)))
              atp-strip $  -- Γ ⊢ (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (¬ p ∧ ¬ q)
              atp-canonicalize $  -- Γ ⊢ ((¬ p ∧ ¬ q) ∧ (p ∨ (q ∧ r)))
                atp-strip $  -- Γ ⊢ (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)
                    atp-neg subgoal₀
            )
            (
            ∧-proj₁ $ -- 1: (¬ p ∧ ¬ q)
              atp-canonicalize $  -- Γ ⊢ ((¬ p ∧ ¬ q) ∧ (p ∨ (q ∧ r)))
                atp-strip $  -- Γ ⊢ (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)
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
          ∧-proj₂ $ -- ((p ∨ (q ∧ r)) ≟ (p ∨ (q ∧ r)))
            atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ (p ∨ q)) ∧ (p ∨ (q ∧ r)))
              atp-strip $  -- Γ ⊢ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ r) ∧ (p ∨ q))
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ (p ∨ q)) ∧ (p ∨ (q ∧ r)))
                atp-strip $  -- Γ ⊢ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                    atp-neg subgoal₁
            )
            (
            ∧-intro
              (
              atp-simplify $  -- Γ ⊢ q
                ∧-intro
                  (
                  ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ r) ∧ (p ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ (p ∨ q)) ∧ (p ∨ (q ∧ r)))
                      atp-strip $  -- Γ ⊢ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                          atp-neg subgoal₁
                  )
                  (
                  ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ r) ∧ (p ∨ q))
                    atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ (p ∨ q)) ∧ (p ∨ (q ∧ r)))
                      atp-strip $  -- Γ ⊢ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                          atp-neg subgoal₁
                  )
              )
              (
              ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ r) ∧ (p ∨ q))
                atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ r) ∧ (p ∨ q)) ∧ (p ∨ (q ∧ r)))
                  atp-strip $  -- Γ ⊢ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)
                      atp-neg subgoal₁
              )
            )
          )

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ q) ∧ (p ∨ q))
            atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ q) ∧ (p ∨ q)) ∧ (p ∨ r))
              atp-strip $  -- Γ ⊢ ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)
                  atp-neg subgoal₂
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ q) ∧ (p ∨ q))
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ q) ∧ (p ∨ q)) ∧ (p ∨ r))
                atp-strip $  -- Γ ⊢ ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)
                    atp-neg subgoal₂
            )
            (
            ∧-proj₁ $ -- 1: ((¬ p ∧ ¬ q) ∧ (p ∨ q))
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ ¬ q) ∧ (p ∨ q)) ∧ (p ∨ r))
                atp-strip $  -- Γ ⊢ ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)
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
          ∧-proj₂ $ -- ((p ∨ r) ≟ (p ∨ r))
            atp-canonicalize $  -- Γ ⊢ ((((¬ p ∧ ¬ r) ∧ q) ∧ (p ∨ q)) ∧ (p ∨ r))
              atp-strip $  -- Γ ⊢ (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                  atp-neg subgoal₃
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (((¬ p ∧ ¬ r) ∧ q) ∧ (p ∨ q))
              atp-canonicalize $  -- Γ ⊢ ((((¬ p ∧ ¬ r) ∧ q) ∧ (p ∨ q)) ∧ (p ∨ r))
                atp-strip $  -- Γ ⊢ (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                    atp-neg subgoal₃
            )
            (
            ∧-proj₁ $ -- 1: (((¬ p ∧ ¬ r) ∧ q) ∧ (p ∨ q))
              atp-canonicalize $  -- Γ ⊢ ((((¬ p ∧ ¬ r) ∧ q) ∧ (p ∨ q)) ∧ (p ∨ r))
                atp-strip $  -- Γ ⊢ (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)
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

