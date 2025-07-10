import Game.Levels.Samarkand.L04_SurjectiveImagePreimage

World "Samarkand"
Level 5

Title "Range of Injective"

Introduction "
  **アラプカ**: 私にも単射写像について質問があります. 
"

open Set

#check Set.singleton

/---/
TheoremDoc Function.Injective.exists_unique_of_mem_range as "Injective.exists_unique_of_mem_range" in "Function"

namespace Function

Statement Injective.exists_unique_of_mem_range {A B : Type} {f : A → B} (hf : Injective f)
    {b : B} (hb : b ∈ range f) :
    ∃! a, f a = b := by
  Hint "**あなた**: `∃! a` でまず使用したい要素 `a` を構築します…

  **Robo**: …そして `use a` と `simp` を適用します. その通りです. 
  "
  obtain ⟨a, ha⟩ := hb
  use a
  simp -- TODO: can this be integrated into mathlib `use`?
  constructor
  · assumption
  · intro a' ha'
    apply hf
    rw [ha',ha]

Conclusion "
  アラプカはまだじっと動かずにいますが, 幸せそうに見えます. 
"
