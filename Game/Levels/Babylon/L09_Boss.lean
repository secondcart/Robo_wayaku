import Game.Metadata

import Game.Levels.Babylon.L08_Induction3_sub_insert3

World "Babylon"
Level 9
Title ""

Introduction
"
まだ遠くまで進んでいないところで、塔の後ろから突然特に大きなバビロニア人が現れ、
道を塞ぎ、険しい顔で睨みつけながら、次の等式の証明を低い声で要求してきます。
"

open Finset
open Robo.NN.Finset -- temporary solution to make correct version of `insert_Icc_eq_Icc_add_one_right` available

-- open BigOperators


Statement (m : ℕ) : (∑ i ∈ Icc 0 m, (i : ℚ) ^3) = (∑ i ∈  Icc 0 m, i : ℚ)^2 := by
  Hint "**あなた**: まあ、きっとうまくいくでしょう…"
  induction m with n n_ih
  · simp
  · rw [← insert_Icc_eq_Icc_add_one_right]
    · rw [sum_insert]
      · simp
        rw [n_ih]
        Hint (hidden := true) "
          **ロボ**: `arithmetic_sum`は既に証明済みだということを覚えておいてください。
        "
        rw [arithmetic_sum]
        simp
        ring
      · simp
    · linarith

TheoremTab "∑ Π"

Conclusion "バビロニア人は長い間考え込み、あなたは彼が決して攻撃的ではなかったこと、
ただ非常に低い声を持っていただけだと感じ始めます。

小さな地震と共に彼は座り込み、感謝の意を込めて手を振ります。"
