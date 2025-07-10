import Game.Metadata
import Game.Levels.Cantor.L10_CantorPowerset

World "Cantor"
Level 11

Title ""

Introduction "
  **カントール**: 簡単？わからないな。でもエレガントだ！

  彼は後方宙返りを3回して、
  あなたたちへの新しいメモを持って戻ってきた。

  **カントール**: 見て！これで同じ論法を使って、
  自然数列の集合、つまり写像`ℕ → ℕ`の集合が
  非可算であることを示せるよ！

  そして小声で：

  **カントール**: このテントには非可算な数の席があるんだ！
"

Conclusion "
  **ロボ**: ご紹介ありがとうございました！

  **あなた**: でも観客が少なくて残念だね！

  **カントール**: 魔法は誰にでも理解できるものじゃないからね。良い旅を！
"


open Nat Set Function

Statement : ¬ ∃ f : ℕ → ℕ → ℕ, Surjective f := by
  push_neg
  intro f
  by_contra hf
  apply cantor_diagonal at hf
  Hint (hidden := true) "
    **あなた**: 写像`n ↦ n + 1`って何て言うんだっけ？

    **ロボ**: `succ`
  "
  specialize hf succ
  obtain ⟨n, hn⟩ := hf
  unfold fixedPoints IsFixedPt at hn
  simp at hn -- dsimp [IsFixedPt] at hn
  --simp only [Nat.succ_ne_self] at hn


TheoremTab "Function"
