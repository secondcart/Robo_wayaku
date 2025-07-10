import Game.Levels.Samarkand.L06_PreimageNonempty


World "Samarkand"
Level 7

Title "Preimage of the inverse"

Introduction "
  **アラプカ**: さて、本当に難しい課題がまだ残っています。
"

open Function Set

-- This is Set.image_subset_preimage_of_inverse in mathlib
Statement  {A B : Type} {f : A → B} {g : B → A}
    (hL : LeftInverse g f) (S : Set A) :
    f '' S ⊆ g ⁻¹' S := by
  Hint "**あなた**: 考えてみよう…∪"
  intro b hb
  obtain ⟨x, hx, e⟩ := hb
  Branch
    dsimp [LeftInverse] at hL
    rw [← hL x, e] at hx
    Branch
      apply hx
    assumption
  unfold LeftInverse at hL
  apply congr_arg g at e
  specialize hL x
  rw [← hL, e] at hx
  assumption

Conclusion "
  **アラプカ**: わあ！あなたたちは本当に素晴らしいです。
"
