{-# LANGUAGE UnicodeSyntax #-}
--------------------------------------------------------------------------------
-- File   : Proof
-- Author : Alejandro Gómez-Londoño
-- Date   : Mon Oct 12 17:18:37 2015
-- Description : proofs for testing
--------------------------------------------------------------------------------
-- Change log :

--------------------------------------------------------------------------------

module Test.Proof where

import Data.TSTP


base1 ∷ [F]
base1 = [
 F {name = "a1",
   role = Axiom,
   formula = PredApp (AtomicWord "a") [],
   source = NoSource
  },
 F {name = "a2",
   role = Axiom,
   formula = PredApp (AtomicWord "b") [],
   source = NoSource
  },
 F {name = "a3",
   role = Axiom,
   formula = BinOp (BinOp (PredApp (AtomicWord "a") []) (:&:) (PredApp (AtomicWord "b") [])) (:=>:) (PredApp (AtomicWord "z") []),
   source = NoSource
  },
 F {name = "a4",
   role = Conjecture,
   formula = PredApp (AtomicWord "z") [],
   source = NoSource
  },
 F {name = "subgoal_0",
   role = Plain,
   formula = PredApp (AtomicWord "z") [],
   source = Inference Strip [] [Parent "a4" []]
  },
 F {name = "negate_0_0",
   role = Plain,
   formula = (:~:) (PredApp (AtomicWord "z") []),
   source = Inference Negate [] [Parent "subgoal_0" []]
  },
 F {name = "normalize_0_0",
   role = Plain,
   formula = (:~:) (PredApp (AtomicWord "z") []),
   source = Inference Canonicalize [] [Parent "negate_0_0" []]
  },
 F {name = "normalize_0_1",
   role = Plain,
   formula = BinOp (BinOp ((:~:) (PredApp (AtomicWord "a") [])) (:|:) ((:~:) (PredApp (AtomicWord "b") []))) (:|:) (PredApp (AtomicWord "z") []),
   source = Inference Canonicalize [] [Parent "a3" []]
  },
 F {name = "normalize_0_2",
   role = Plain,
   formula = PredApp (AtomicWord "a") [],
   source = Inference Canonicalize [] [Parent "a1" []]
  },
 F {name = "normalize_0_3",
   role = Plain,
   formula = PredApp (AtomicWord "b") [],
   source = Inference Canonicalize [] [Parent "a2" []]
  },
 F {name = "normalize_0_4",
   role = Plain,
   formula = PredApp (AtomicWord "z") [],
   source = Inference Simplify [] [Parent "normalize_0_1" [],
                                   Parent "normalize_0_2" [],
                                   Parent "normalize_0_3" []]
  },
 F {name = "normalize_0_5",
   role = Plain,
   formula = PredApp (AtomicWord "$false") [],
   source = Inference Simplify [] [Parent "normalize_0_0" [],
                                   Parent "normalize_0_4" []]
   },
 F {name = "refute_0_0",
   role = Plain,
   formula = Quant All [] (PredApp (AtomicWord "$false") []),
   source = Inference Canonicalize [] [Parent "normalize_0_5" []]
   }]
