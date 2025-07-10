import Game.Metadata

World "Quantus"
Level 5

Title ""

Introduction
"また別の質問が届きました. どうやらこれは敵陣営からのもののようです. "

open Nat

Statement (i : ℕ) (h : Odd i): (-1 : ℤ)^i  + 1 = 0 := by
  Hint "
    **Robo**: ここは`Odd.neg_pow`を使えば解けると思います. 
  "
  rw [Odd.neg_pow]
  ring
  assumption

/---/
TheoremDoc Odd.neg_pow as "Odd.neg_pow" in "ℕ"

/---/
TheoremDoc Even.neg_pow as "Even.neg_pow" in "ℕ"

NewTheorem Odd.neg_pow Even.neg_pow


Conclusion ""
