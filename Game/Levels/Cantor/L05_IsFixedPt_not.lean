import Game.Metadata
import Game.Levels.Cantor.L04_fixedPoints_neg

World "Cantor"
Level 5

Title ""

Introduction ""

Conclusion "
  **カントール**: 君たちは真相に近づいている…

   雀たちは——驚くことではないが——飛び去ってしまった。
   彼は再びサボテンをジャグリングしながら, 一輪車に乗り続けている。
"

open Function Set

Statement : ¬ ∃ (P : Prop),  IsFixedPt (¬ .) P := by
  Hint "**あなた**: ここで2つ目の`¬`はどういう意味ですか？

  **Robo**: 1つ目と同じです：論理否定です。
  これは可能な命題すべての集合`Prop`の自己写像と見なせます。
  そしてこの写像には当然ながら不動点はありません, 
  なぜなら命題がその否定と等しくなることはあり得ないからです！
  "
  Branch
    by_contra h
    obtain ⟨P, hP⟩ := h
    unfold IsFixedPt at hP
    simp at hP -- a bit magical
  Branch
    push_neg
    intro P h
    unfold IsFixedPt at h
    Branch
      simp_all only [eq_iff_iff]
      simp only [not_iff_self] at h
    tauto
  unfold IsFixedPt
  simp -- or: tauto, but `simp` is better as we want to repeat this proof with `simp at` later
