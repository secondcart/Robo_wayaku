import Game.Metadata

World "Piazza"
Level 12

Title ""

Introduction "
  **Fin**: 正解です. では, ピスタチオを元の場所に戻します.
"

open Set

Statement (A : Finset ℕ) (a : ℕ) :  insert a A = A ∪ {a} := by
  ext
  simp
  tauto

TheoremTab "Set"

Conclusion ""
