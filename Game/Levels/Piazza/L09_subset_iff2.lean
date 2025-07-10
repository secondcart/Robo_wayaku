import Game.Metadata

World "Piazza"
Level 9

Title "" -- "Teilmengen"

Introduction
"
**Sub**: さてさて。ただの定義ですね！
では、このような包含関係で作業する場合どうすればいいのでしょうか？
"

open Set

Statement {A B C : Set ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  -- Hint: do this for understanding the def!
  Hint "
    **あなた**: ここで`ext`を使って議論することはできますか？

    **ロボ**: いいえ、もっと簡単です。`intro a`でAの任意の要素を取り、
    それがCに含まれることを示してください。

    ただし、まず`rw [subset_iff] at *`ですべての包含関係を展開して、
    何が起こるか確認した方が良いかもしれません。
  "
  rw [subset_iff] at *
  -- tauto -- would work here
  intro a ha
  apply h₁ at ha
  apply h₂ at ha
  assumption

DisabledTactic tauto

NewDefinition Subset

TheoremTab "Set"

Conclusion ""
