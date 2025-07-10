import Game.Metadata
import Game.Levels.Cantor.L03_IsFixedPt_abs

World "Cantor"
Level 4

Title ""

Introduction
""

Conclusion "
  **カントール**: その調子で続けてください！

  彼はサボテンをスズメと交換しました。
"
open Function Set

Statement :
    fixedPoints (fun (x : ℝ) ↦ -x) = {0} := by
  Hint (strict := true) "
    **あなた**: ここで`fixedPoints f`はおそらくすべての不動点の集合ですか？

    **ロボット**: 試してみてください - `unfold`がまた役立つはずです。
  "
  unfold fixedPoints
  Hint (strict := true)  "
    **ロボット**: 良さそうです。そして今すぐ`unfold IsFixedPt`もするのが良いでしょう。
  "
  unfold IsFixedPt
  Hint (strict := true) (hidden := true) "
    **ロボット**: `simp`はいつでも試してみる価値があります…
  "
  simp
  /-
  Branch
    rw [Subset.antisymm_iff]
  ext x
  constructor
  · intro h
    simp at h
    assumption
    -- rw [mem_fixedPoints_iff] at h
  · intro h
    simp at h --or: rw [mem_singleton_iff] at h
    rw [h]
    -- rw [mem_fixedPoints_iff]
    simp
-/

NewDefinition Function.fixedPoints
