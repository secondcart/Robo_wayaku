import Game.Metadata
import Game.Levels.Babylon.L06_Induction_sum_insert__arithmetic_sum

World "Babylon"
Level 7

Title ""

Introduction
"Gaussの塔のすぐ隣に, 再び空き地があります.  今回は看板に次のように書かれています："

open Finset
open Robo.ZZ.Finset -- temporary solution to make correct version of `insert_Icc_eq_Icc_add_one_right` available


Statement  (n : ℕ) : ∑ i ∈ Icc (-n : ℤ) n, i = 0 := by
    Hint "
      **あなた**:  $\\sum_\{i=-n}^{n} i = 0$ – はい, これは正しいようです. 

      **Robo**: 先ほどのGauss和と同じように証明できるはずです…
      ただし, `insert_Icc_eq_Icc_add_one_right` の後には
      `insert_Icc_eq_Icc_sub_one_left` も必要になるでしょう. 
    "
    induction n with d hd
    · simp
    · simp
      rw [← insert_Icc_eq_Icc_add_one_right]
      Hint (hidden := true) "
        **Robo**: その通り, 今度も `rw [sum_insert]` を使ってください. 
        "
      · rw [sum_insert]
        Hint "
          **Robo**: 次は `-1 + -{d}` を `-{d} - 1` と書き換える必要があります. 
          おそらく, この等式を `have` で表現するのが最も簡単でしょう. 
          ℤ における等式であることを明確にする必要があります. 
          例えば次のように：
          ```
          have : -1 + (-d : ℤ)  = -d - 1
          ```
        "
        · --have : (-1 : ℤ)  + -↑d  = -↑d - 1 := by
          have : -1 + (-d : ℤ)  = -d - 1 := by
            ring
          rw [this]
          rw [← insert_Icc_eq_Icc_sub_one_left]
          · rw [sum_insert]
            · rw [hd]
              ring
            · simp
          · --omega -- fails; omega appears to treat ↑d as a random integer rather than a natural number
            linarith
        · simp
      · linarith

TheoremTab "∑ Π"

Conclusion ""
