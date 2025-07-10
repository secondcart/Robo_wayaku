import Game.Metadata

import Game.Levels.Quantus

World "Spinoza"
Level 6

Title "Contradiction"

Introduction
"
**あなた**: でも, 前の問題は矛盾による証明でも同じように解けませんでしたか？

**ベネディクトゥス**: もちろんです. ただ, 二度目の矛盾証明は退屈だと思っただけです. 
ですが, この問題をもう一度試してみるのは自由ですよ. 
ほら, 旅のお供にこれを差し上げましょう. 
さあ, 先に進んでください！"

open Nat

Statement (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  Hint "
    小惑星の重力圏から無事に離脱したら, 再び問題に取り掛かります. 

    **Roboット**: よし, 今回は `by_contra g` から始めよう！"
  by_contra g
  Hint "**Roboット**: 今度は `Odd (n ^ 2)` との矛盾を導きたいな. "
  Hint (hidden := true) "**Roboット**: つまり `suffices d : ¬ Odd (n ^ 2)` だ. "
  suffices d : ¬ Odd (n ^ 2)
  contradiction
  rw [←even_iff_not_odd] at *
  apply even_square
  assumption

DisabledTactic contrapose revert

Conclusion "
**Roboット**: ブラボー！ベネディクトゥスが教えてくれたことをまとめましょう. 


| **戦術**      | **目的**                                              |
|:----------------|:-------------------------------------------------------|
| `have`          | 中間結果を仮定する                              |
| `suffices`      | 中間結果を仮定する                              |
| `by_contra`     | 矛盾証明を開始する                            |
| `contradiction` | 矛盾証明を終了する                           |
| `contrapose`    | 対偶法                                         |
| `revert`        | `contrapose` を適用する前に有用            |
"
