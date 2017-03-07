
-- tstp2agda proof

open import Data.FOL.Deep 4 public
open import Data.FOL.Deep.ATP.Metis 4 public

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

r : Prop
r = Var (# 2)

s : Prop
s = Var (# 3)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (((p ∧ (q ⇒ r)) ⇒ s) ⇔ (((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((((p ∧ (q ⇒ r)) ⇒ s) ∧ ¬ ¬ p) ∧ ¬ q) ⇒ s)


subgoal₁ : Prop
subgoal₁ = ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)


subgoal₂ : Prop
subgoal₂ = ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- (((¬ p ∨ s) ∨ (¬ r ∧ q)) ≟ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
            atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ ¬ s) ∧ p) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
              atp-strip $  -- Γ ⊢ (((((p ∧ (q ⇒ r)) ⇒ s) ∧ ¬ ¬ p) ∧ ¬ q) ⇒ s)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∧ (q ⇒ r)) ⇒ s) ∧ ¬ ¬ p) ∧ ¬ q) ⇒ s)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((¬ q ∧ ¬ s) ∧ p)
              atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ ¬ s) ∧ p) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
                atp-strip $  -- Γ ⊢ (((((p ∧ (q ⇒ r)) ⇒ s) ∧ ¬ ¬ p) ∧ ¬ q) ⇒ s)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∧ (q ⇒ r)) ⇒ s) ∧ ¬ ¬ p) ∧ ¬ q) ⇒ s)
                    atp-neg subgoal₀
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 1: ((¬ q ∧ ¬ s) ∧ p)
                atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ ¬ s) ∧ p) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
                  atp-strip $  -- Γ ⊢ (((((p ∧ (q ⇒ r)) ⇒ s) ∧ ¬ ¬ p) ∧ ¬ q) ⇒ s)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∧ (q ⇒ r)) ⇒ s) ∧ ¬ ¬ p) ∧ ¬ q) ⇒ s)
                      atp-neg subgoal₀
              )
              (
              ∧-proj₁ $ -- 1: ((¬ q ∧ ¬ s) ∧ p)
                atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ ¬ s) ∧ p) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
                  atp-strip $  -- Γ ⊢ (((((p ∧ (q ⇒ r)) ⇒ s) ∧ ¬ ¬ p) ∧ ¬ q) ⇒ s)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ∧ (q ⇒ r)) ⇒ s) ∧ ¬ ¬ p) ∧ ¬ q) ⇒ s)
                      atp-neg subgoal₀
              )
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- (((¬ p ∨ s) ∨ (¬ r ∧ q)) ≟ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
            atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s)) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
              atp-strip $  -- Γ ⊢ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s))
              atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s)) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
                atp-strip $  -- Γ ⊢ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                    atp-neg subgoal₁
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s))
                atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s)) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
                  atp-strip $  -- Γ ⊢ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                      atp-neg subgoal₁
              )
              (
              ∧-intro
                (
                ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s))
                  atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s)) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
                    atp-strip $  -- Γ ⊢ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                        atp-neg subgoal₁
                )
                (
                atp-simplify $  -- Γ ⊢ q
                  ∧-intro
                    (
                    ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s))
                      atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s)) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
                        atp-strip $  -- Γ ⊢ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                          assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                            atp-neg subgoal₁
                    )
                    (
                    ∧-intro
                      (
                      ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s))
                        atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s)) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
                          atp-strip $  -- Γ ⊢ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                              atp-neg subgoal₁
                      )
                      (
                      ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s))
                        atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ r) ∧ ((¬ p ∨ q) ∨ s)) ∧ ((¬ p ∨ s) ∨ (¬ r ∧ q)))
                          atp-strip $  -- Γ ⊢ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((p ∧ (q ⇒ r)) ⇒ s) ∧ ((¬ p ∨ q) ∨ s)) ∧ ¬ ¬ p) ∧ ¬ ¬ r) ⇒ s)
                              atp-neg subgoal₁
                      )
                    )
                )
              )
            )
          )

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ q r : Set} → ¬ q ∨ r)
      ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
        atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
          atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
              atp-neg subgoal₂

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ q : Set} → q)
      atp-simplify $  -- Γ ⊢ q
        ∧-intro
          (
          ∧-proj₂ $ -- (((¬ p ∨ q) ∨ s) ≟ ((¬ p ∨ q) ∨ s))
            atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
              atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                  atp-neg subgoal₃
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
              atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                    atp-neg subgoal₃
            )
            (
            ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
              atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                    atp-neg subgoal₃
            )
          )

proof₄ : Γ ⊢ subgoal₄
proof₄ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ q : Set} → q)
          atp-simplify $  -- Γ ⊢ q
            ∧-intro
              (
              ∧-proj₂ $ -- (((¬ p ∨ q) ∨ s) ≟ ((¬ p ∨ q) ∨ s))
                atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                  atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                      atp-neg subgoal₄
              )
              (
              ∧-intro
                (
                ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
                  atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                    atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                        atp-neg subgoal₄
                )
                (
                ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
                  atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                    atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                        atp-neg subgoal₄
                )
              )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ q r : Set} → ¬ q ∨ r)
          ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
            atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
              atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                  atp-neg subgoal₄
      )

proof₅ : Γ ⊢ subgoal₅
proof₅ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ r : Set} → ¬ r)
      atp-simplify $  -- Γ ⊢ ¬ r
        ∧-intro
          (
          ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
            atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
              atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                  atp-neg subgoal₅
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
              atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                    atp-neg subgoal₅
            )
            (
            ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
              atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                    atp-neg subgoal₅
            )
          )

proof₆ : Γ ⊢ subgoal₆
proof₆ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ q : Set} → q)
              atp-simplify $  -- Γ ⊢ q
                ∧-intro
                  (
                  ∧-proj₂ $ -- (((¬ p ∨ q) ∨ s) ≟ ((¬ p ∨ q) ∨ s))
                    atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                      atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                          atp-neg subgoal₆
                  )
                  (
                  ∧-intro
                    (
                    ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
                      atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                        atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                          assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                            atp-neg subgoal₆
                    )
                    (
                    ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
                      atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                        atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                          assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                            atp-neg subgoal₆
                    )
                  )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ q r : Set} → ¬ q ∨ r)
              ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
                atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                  atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                      atp-neg subgoal₆
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ r : Set} → ¬ r)
          atp-simplify $  -- Γ ⊢ ¬ r
            ∧-intro
              (
              ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
                atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                  atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                      atp-neg subgoal₆
              )
              (
              ∧-intro
                (
                ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
                  atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                    atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                        atp-neg subgoal₆
                )
                (
                ∧-proj₁ $ -- 1: (((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s))
                  atp-canonicalize $  -- Γ ⊢ ((((¬ s ∧ p) ∧ (¬ q ∨ r)) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ ((¬ p ∨ q) ∨ s))
                    atp-strip $  -- Γ ⊢ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                      assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((((¬ p ∨ q) ∨ s) ∧ ((¬ p ∨ ¬ r) ∨ s)) ∧ p) ∧ (q ⇒ r)) ⇒ s)
                        atp-neg subgoal₆
                )
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
        subgoal₂
      )
    )

