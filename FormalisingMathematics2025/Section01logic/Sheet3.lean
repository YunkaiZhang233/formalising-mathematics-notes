/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro hNT
  change True → False at hNT
  apply hNT
  trivial
  done

example : False → ¬True := by
  intro hF
  by_contra hnnT
  assumption
  done

example : ¬False → True := by
  intro hNF
  by_contra hnT
  change True → False at hnT
  apply hnT
  trivial
  done

example : True → ¬False := by
  intro ht
  change False → False
  intro hf
  assumption
  done

example : False → ¬P := by
  intro hf
  exfalso
  assumption
  done

example : P → ¬P → False := by
  intro hP hNP
  change P → False at hNP
  by_cases P <;> apply hNP <;> assumption
  done

example : P → ¬¬P := by
  intro hP
  by_contra hnP
  apply hnP
  assumption
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ
  change P → False
  intro hP
  apply hPQ at hP
  apply hnQ at hP
  assumption
  done

example : ¬¬False → False := by
  intro hnnF
  by_contra hnF
  change ¬False → False at hnnF
  apply hnnF at hnF
  exact hnF
  done

example : ¬¬P → P := by
  intro hnnP
  change ¬P → False at hnnP
  by_cases h : P
  · exact h
  · exfalso
    apply hnnP
    exact h
  done

example : (¬Q → ¬P) → P → Q := by
  intro hnQnP
  intro hnP
  by_cases hQ : Q
  · assumption
  · apply hnQnP at hQ
    change P → False at hQ
    exfalso
    apply hQ
    assumption
  done
