import Game.Metadata


open Nat

World "Luna"
Level 4

Title ""

Introduction
"
  **Lina**:  ここにまだ何かあるわ. 
"

Statement (l m n x : ℕ) (h₁ : l ≤ m) (h₂ : m ≤ n) : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  Hint "Rithaが目で何か合図を送ろうとしているようだ. "
  omega

TheoremTab "ℕ"

Conclusion "
  **Lina**:  はい, わかった, 私のミスね. 
"
