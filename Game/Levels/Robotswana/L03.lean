import Game.Levels.Robotswana.L02_EBasis

World "Robotswana"
Level 3

Title "" -- "Richtige Indizes"

Introduction ""

Conclusion "
  **あなた**: でも, 誰がここにメモを落としたり捨てたりしたのか気になってきたな。さあ, 先に進もう。
"

open Nat Matrix

/---/
TheoremDoc Matrix.E.mul_same as "E.mul_same" in "Matrix"

-- @[inherit_doc Matrix.StdBasisMatrix.mul_same]
Statement Matrix.E.mul_same {n : ℕ} (i j k : Fin n) : E i j * E j k = E i k  := by
  Hint "**あなた**: これも正しそうだ。"
  unfold E
  simp

TheoremTab "Matrix"
