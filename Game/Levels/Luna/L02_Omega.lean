import Game.Metadata


open Nat

World "Luna"
Level 2

Title ""

Introduction
"
**Lina** 例えば, 整数において`0 < n`や`n < 0`は`n ≠ 0`と同じ意味だということを知っておく必要があります.
"

Statement (n : ℤ) : 0 < n ∨ n < 0 ↔ n ≠ 0 := by
  Hint "**Ritha** *(小声で)* `omega`を試してみて! "
  omega

NewTactic omega

TheoremTab "ℕ"

Conclusion "Linaは目を回す.

**Lina** Rithaは`omega`の大ファンなの. でも`omega`は結構無力なのよ.
整数の範囲を超えたら, `omega`は何もできなくなっちゃう.

**Ritha** あなたこそ無力よ!

Rithaは下品な顔をする.
"
