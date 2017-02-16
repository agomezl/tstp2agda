
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
a₃ = (((¬ a ∧ b) ∨ (¬ b ∧ a)) ∨ ((a ∧ b) ∧ c))


a₄ : Prop
a₄ = (¬ c ∨ d)


-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2 , a3 , a4

-- Conjecture
a₅ : Prop
a₅ = d


-- Subgoal
subgoal₀ : Prop
subgoal₀ = d

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
  -- Γ , ¬ subgoal₀⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀
          )
          (
          atp-simplify $
            ∧-intro
              (
              atp-canonicalize $
                weaken (atp-neg subgoal₀) $
                  (assume {Γ = ∅} a4)
              )
              (
              atp-simplify $
                ∧-intro
                  (
                  atp-canonicalize $
                    weaken (atp-neg subgoal₀) $
                      (assume {Γ = ∅} a3)
                  )
                  (
                  ∧-intro
                    (
                    atp-canonicalize $
                      weaken (atp-neg subgoal₀) $
                        (assume {Γ = ∅} a1)
                    )
                    (
                    ∧-intro
                      (
                      atp-canonicalize $
                        weaken (atp-neg subgoal₀) $
                          (assume {Γ = ∅} a2)
                      )
                      (
                      ∧-intro
                        (
                        atp-canonicalize $
                          weaken (atp-neg subgoal₀) $
                            (assume {Γ = ∅} a2)
                        )
                        (
                        ∧-intro
                          (
                          atp-canonicalize $
                            weaken (atp-neg subgoal₀) $
                              (assume {Γ = ∅} a1)
                          )
                          (
                          ∧-intro
                            (
                            atp-canonicalize $
                              weaken (atp-neg subgoal₀) $
                                (assume {Γ = ∅} a1)
                            )
                            (
                            atp-canonicalize $
                              weaken (atp-neg subgoal₀) $
                                (assume {Γ = ∅} a2)
                            )
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
    proof₀

