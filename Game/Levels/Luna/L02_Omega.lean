import Game.Metadata


open Nat

World "Luna"
Level 2

Title ""

Introduction
"
**リナ**: 例えば, 整数において`0 < n`や`n < 0`は`n ≠ 0`と同じ意味だということを知っておく必要があります。
"

Statement (n : ℤ) : 0 < n ∨ n < 0 ↔ n ≠ 0 := by
  Hint "**リタ** *(小声で)*: `omega`を試してみて！"
  omega

NewTactic omega

TheoremTab "ℕ"

Conclusion "リナは目を回す。

**リナ**: リタは`omega`の大ファンなの。でも`omega`は結構無力なのよ。
整数の範囲を超えたら, `omega`は何もできなくなっちゃう。

**リタ**: あなたこそ無力よ！

リタは下品な顔をする。
"
