import Game.Metadata

World "Piazza"
Level 10

Title ""

Introduction
"
**Mem** 私ももう一度質問させてください!
"

open Set Nat -- Nat is opened in case someone wants to use `Nat.even_iff_not_odd` here

Statement : {2, 7} ⊆ {2} ∪ { n : ℕ | Odd n} := by
  Hint (hidden := true) "
    **Robo** 私はまた`intro`から始めます.
  "
  intro x
  Hint (hidden := true) "
    **Robo** もう一度`intro`を!
  "
  intro hx
  simp at *
  obtain h | h := hx
  · tauto -- or  left, assumption
  · right
    rw [h]
    decide

TheoremTab "Set"

Conclusion "
**Mem** はい, 素晴らしい! でもあなたたちは早く覚えましたね!
"
