import Game.Metadata
import Game.Levels.Cantor.L05_IsFixedPt_not

World "Cantor"
Level 6

Title ""

Introduction ""

Conclusion "
  カントールはまた何か言っていますが, あなた方は問題に夢中です。
  彼が一輪車で飛び始めたことさえ気づいていません。
"

open Function Set

Statement {f : ℝ → ℝ} (h_odd : ∀ x, f (-x) = - f x) (x : ℝ) :
    IsFixedPt f x ↔ IsFixedPt f (- x) := by
  Hint "
    **あなた**: 似たようなものを見たことがあります
    ― この仮定は`f`が「奇関数」であることを示しています。

    **Roboット**: では始めましょう。これまでに見たことのないものは必要ないと思います。
    "
  constructor
  · intro h
    unfold IsFixedPt
    rw [h_odd x]
    rw [h]
  · intro h
    unfold IsFixedPt at h
    rw [h_odd x] at h
    simp at h
    --rw [neg_inj] at h
    assumption

-- /---/
-- TheoremDoc neg_inj as "neg_inj" in "Function"
--
-- NewTheorem neg_inj
-- TheoremTab "Function"
