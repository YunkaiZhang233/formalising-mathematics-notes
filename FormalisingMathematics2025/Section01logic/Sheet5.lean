/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;> intro h <;> rw [h]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rw [← h1] at h2
  exact h2
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;> intro h <;> cases' h with hP hQ <;> constructor <;> assumption
  done

-- To Ask in the Labs
example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor <;> intro h <;> cases' h with h1 h2
  · cases' h1 with ha hb
    constructor
    · assumption
    · constructor <;> assumption
  · cases' h2 with hc hd
    constructor
    · constructor <;> assumption
    · assumption
  done

example : P ↔ P ∧ True := by
  constructor <;> intro h
  · constructor
    · assumption
    · trivial
  · cases' h with h1 h2
    assumption
  done

example : False ↔ P ∧ False := by
  constructor <;> intro h <;> exfalso
  · assumption
  · cases' h with h1 h2
    assumption
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  rw [h1, h2]
  done

example : ¬(P ↔ ¬P) := by
  by_contra h
  by_cases hP : P
  -- P holds
  · cases' h with h1 h2
    have h' := hP
    apply h1 at h'
    change P → False at h'
    apply h'
    assumption
  -- not P holds
  · cases' h with h1 h2
    have h' := hP
    change P → False at h'
    apply h'
    apply h2
    assumption
  done
