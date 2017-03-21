
-- tstp2agda proof

open import Data.FOL.Deep 4 public
open import Data.FOL.Deep.ATP.Metis 4 public

-- Vars
a : Prop
a = Var (# 0)

b : Prop
b = Var (# 1)

c : Prop
c = Var (# 2)

d : Prop
d = Var (# 3)

-- Axioms
a₁ : Prop
a₁ = a


a₂ : Prop
a₂ = b


a₃ : Prop
a₃ = ((¬ a ∨ ¬ b) ∨ c)


a₄ : Prop
a₄ = (¬ c ∨ d)


-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2 , a3 , a4

-- Conjecture
a₅ : Prop
a₅ = ((d ∧ a) ∨ (b ∧ c))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (¬ (d ∧ a) ⇒ b)


subgoal₁ : Prop
subgoal₁ = ((¬ (d ∧ a) ∧ b) ⇒ c)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ (¬ b ∧ (¬ a ∨ ¬ d))
            atp-strip $  -- Γ ⊢ (¬ (d ∧ a) ⇒ b)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ (¬ (d ∧ a) ⇒ b)
                atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-canonicalize $  -- Γ ⊢ b
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} a2)
            )
            (
            ∧-intro
              (
              atp-canonicalize $  -- Γ ⊢ a
                weaken (atp-neg subgoal₀) $
                  (assume {Γ = ∅} a1)
              )
              (
              atp-simplify $  -- Γ ⊢ d
                ∧-intro
                  (
                  atp-canonicalize $  -- Γ ⊢ (¬ c ∨ d)
                    weaken (atp-neg subgoal₀) $
                      (assume {Γ = ∅} a4)
                  )
                  (
                  atp-simplify $  -- Γ ⊢ c
                    ∧-intro
                      (
                      atp-canonicalize $  -- Γ ⊢ ((¬ a ∨ ¬ b) ∨ c)
                        weaken (atp-neg subgoal₀) $
                          (assume {Γ = ∅} a3)
                      )
                      (
                      ∧-intro
                        (
                        atp-canonicalize $  -- Γ ⊢ a
                          weaken (atp-neg subgoal₀) $
                            (assume {Γ = ∅} a1)
                        )
                        (
                        atp-canonicalize $  -- Γ ⊢ b
                          weaken (atp-neg subgoal₀) $
                            (assume {Γ = ∅} a2)
                        )
                      )
                  )
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
          atp-canonicalize $  -- Γ ⊢ ((¬ c ∧ b) ∧ (¬ a ∨ ¬ d))
            atp-strip $  -- Γ ⊢ ((¬ (d ∧ a) ∧ b) ⇒ c)
              assume {Γ = Γ} $  -- Γ ⊢ ¬ ((¬ (d ∧ a) ∧ b) ⇒ c)
                atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            atp-simplify $  -- Γ ⊢ c
              ∧-intro
                (
                atp-canonicalize $  -- Γ ⊢ ((¬ a ∨ ¬ b) ∨ c)
                  weaken (atp-neg subgoal₁) $
                    (assume {Γ = ∅} a3)
                )
                (
                ∧-intro
                  (
                  atp-canonicalize $  -- Γ ⊢ a
                    weaken (atp-neg subgoal₁) $
                      (assume {Γ = ∅} a1)
                  )
                  (
                  atp-canonicalize $  -- Γ ⊢ b
                    weaken (atp-neg subgoal₁) $
                      (assume {Γ = ∅} a2)
                  )
                )
            )
            (
            ∧-intro
              (
              atp-canonicalize $  -- Γ ⊢ b
                weaken (atp-neg subgoal₁) $
                  (assume {Γ = ∅} a2)
              )
              (
              ∧-intro
                (
                atp-canonicalize $  -- Γ ⊢ a
                  weaken (atp-neg subgoal₁) $
                    (assume {Γ = ∅} a1)
                )
                (
                atp-simplify $  -- Γ ⊢ d
                  ∧-intro
                    (
                    atp-canonicalize $  -- Γ ⊢ (¬ c ∨ d)
                      weaken (atp-neg subgoal₁) $
                        (assume {Γ = ∅} a4)
                    )
                    (
                    atp-simplify $  -- Γ ⊢ c
                      ∧-intro
                        (
                        atp-canonicalize $  -- Γ ⊢ ((¬ a ∨ ¬ b) ∨ c)
                          weaken (atp-neg subgoal₁) $
                            (assume {Γ = ∅} a3)
                        )
                        (
                        ∧-intro
                          (
                          atp-canonicalize $  -- Γ ⊢ a
                            weaken (atp-neg subgoal₁) $
                              (assume {Γ = ∅} a1)
                          )
                          (
                          atp-canonicalize $  -- Γ ⊢ b
                            weaken (atp-neg subgoal₁) $
                              (assume {Γ = ∅} a2)
                          )
                        )
                    )
                )
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
      subgoal₁
    )

