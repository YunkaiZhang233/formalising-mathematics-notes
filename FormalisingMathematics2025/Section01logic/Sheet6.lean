/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP
  done

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ
  done

-- inlining
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  intro hPR hQR
  cases hPoQ with
  | inl h => apply hPR; assumption
  | inr h => apply hQR; assumption
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases h
  case inl hP => right; assumption
  case inr hP => left; assumption
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor <;> intro h
  -- case 1: (P V Q) V R -> P V (Q v R)
  · cases' h with h1 h2
    · cases h1
      case inl hP => left; exact hP
      case inr hQ => right; left; exact hQ
    · right; right; exact h2
  -- case 2: P V (Q V R) -> (P V Q) v R
  · cases' h with h1 h2
    · left; left; exact h1
    · cases h2
      case inl hQ => left; right; exact hQ
      case inr hR => right; exact hR
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS h
  cases h
  case inl hP =>
    left
    apply hPR
    exact hP
  case inr hQ =>
    right
    apply hQS
    exact hQ
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPR
  cases hPR
  case inl hP =>
    left
    apply hPQ
    assumption
  case inr hR =>
    right
    exact hR
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPR hQS
  rw [hPR, hQS]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor <;> intro h
  · constructor
    · change P → False
      intro hP
      have hPQ : P ∨ Q := by left; exact hP
      apply h
      exact hPQ
    · change Q → False
      intro hQ
      change P ∨ Q -> False at h
      apply h
      right
      exact hQ
  · change P ∨ Q → False
    intros hPQ
    cases' h with hnP hnQ
    cases hPQ
    case inl hP => apply hnP; exact hP
    case inr hQ => apply hnQ; exact hQ
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor <;> intro h
  · -- left
    by_cases hP : P
    · -- P holds
      by_cases hQ : Q
      · -- Q holds
        exfalso
        have hPQ : P ∧ Q := by constructor <;> assumption
        change P ∧ Q → False at h
        apply h at hPQ
        exact hPQ
      · -- not Q holds
        right
        exact hQ
    · -- not P holds
      left
      exact hP
  · -- right
    change P ∧ Q → False
    intro hPQ
    cases' hPQ with hP hQ
    cases h with
    | inl hnP => apply hnP; exact hP
    | inr hnQ => apply hnQ; exact hQ
  done
