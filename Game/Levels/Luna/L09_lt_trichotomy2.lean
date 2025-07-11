import Game.Metadata

World "Luna"
Level 9

Title ""

Introduction "
**Lina**: 今度は私の番ね. 
"

open Finset
Statement (a c : ℝ) (h : a ≠ c): ∃ b : ℝ, a < b ∧ b < c ∨ c < b ∧ b < a := by
  Hint "**あなた**:
  さて, ここでどの`b`を使うべきかはかなり明白ですね. 

  **Robo**: そんなに明白なら, まず`use …`から始めてみたらどうですか. 
  その後, `lt_trichotomy`が役に立つでしょう. 例えばこうです：
  ```
  obtain h | h | h := lt_trichotomy a c
  ```
  "
  use (a + c) / 2
  obtain h | h | h := lt_trichotomy a c
  · left
    constructor
    linarith
    linarith
  · contradiction
  · right
    constructor
    linarith
    linarith

Conclusion "
  **Lina**: よくできました! 残念ながらもう出発しなければならないのですね. 
  でも, もっと長くいると私たちの生活リズムが完全に乱れてしまいますから. 
  "
