import Game.Metadata

World "Piazza"
Level 5

Title ""

Introduction
"
  **Mem:** この発言もまた混乱させられると思いませんか？
"
namespace Set

Statement : { n : ℕ | Even n } ∩ { n : ℕ | Odd n } = ∅ := by
  Hint "
    **あなた**: いいえ, `∅`は知っています。

    **ロボ**: あなたが正しく理解していることを完全に確認するために, 
    `rw [eq_empty_iff_forall_not_mem]`で始めることもできます。
    または, 早く終わらせたい場合は`simp [eq_empty_iff_forall_not_mem]`を使うこともできます。
  "
  /- Want `eq_empty_iff_forall_not_mem` to be introduced here,
     because it is needed in SAMARKAND!
  -/
  Branch
     ext
     simp
  rw [eq_empty_iff_forall_not_mem]
  simp

TheoremTab "Set"

/---/
TheoremDoc Set.eq_empty_iff_forall_not_mem as "eq_empty_iff_forall_not_mem" in "Set"
NewTheorem Set.eq_empty_iff_forall_not_mem

NewDefinition Set.empty

Conclusion ""
