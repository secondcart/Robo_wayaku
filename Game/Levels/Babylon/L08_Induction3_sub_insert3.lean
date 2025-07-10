import Game.Metadata
import Game.Levels.Babylon.L07_Induction2_sum_insert2

World "Babylon"
Level 8

open Finset
open Robo.NN.Finset -- temporary solution to make correct version of `insert_Icc_eq_Icc_add_one_right` available

-- open BigOperators

Title ""

Introduction
"
純粋な好奇心から、あなたは別の隣の塔をさらに詳しく見ています。
"

Statement (n : ℕ) : (∑ i ∈ Icc 0 n, (2 * i + 1)) = (n + 1)^ 2 := by
  Hint "
    **あなた**: ここでは奇数のみの和ですね。
    $$
    \\sum_\{i = 0}^n (2i + 1) = n^2
    $$

    **ロボ**: 前回と全く同じように解けますよ。
    "
  induction n with d hd
  · simp
  · rw [← insert_Icc_eq_Icc_add_one_right]
    · rw [sum_insert]
      · rw [hd]
        ring
      · simp
    · linarith

TheoremTab "∑ Π"

Conclusion "
  **バビロニア人**: どうですか？ ここは気に入りましたか？

  **ロボ**: はい、とても。ここに築かれたものは全て本当に印象的です。
  しかし、これ以上あなた方の時間を奪いたくありません。

  **あなた**: そろそろ出発した方がいいと思います。

  あなた方は別れの挨拶をし、宇宙船へと戻る道を歩き始めます。
"
