import Game.Metadata


open Nat

World "Luna"
Level 1

Title ""

Introduction
"
少し圧倒された気分ですが, それでも会話を始めようと試みます. 

**あなた**: 大丈夫です, 私たちは混乱を起こさないよう努めています. ここで秩序を保つのはとても大変ですか？

**リナ**: 例えば, `n ≤ n` であることを知っておく必要があります. 
"

Statement (n : ℕ) : n ≤ n := by
  Hint "**Robo**: `rfl`でどう？"
  rfl

Conclusion "
  **リナ**: 認めますが, これは些細な例でした. 
"


/---/
TheoremDoc not_le as "not_le" in "≤"
NewTheorem not_le
-- wird später in Vieta einmal erwähnt, aber nirgends gebraucht
