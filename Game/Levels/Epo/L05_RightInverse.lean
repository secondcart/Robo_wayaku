import Game.Metadata

World "Epo"
Level 5

Title ""


Introduction ""

open Function

Statement :
    let f : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ (m + n, m + 2 * n)
    HasRightInverse f := by
  Hint "
  **あなた**: ここではおそらく, `f`に対する右逆元が存在することを示す必要があるのでしょうか？

  **ロボ**: はい。ですから, まず`let g : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ …`で写像を定義し, 
  それを`use g`で使用できます。

  **あなた**: わかりました。では, `f`の右逆元がどのようなものか考えてみましょう…"
  let g : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ (2 * m - n, n - m)
  use g
  intro m
  simp [g, f]
  ring

NewDefinition Function.HasRightInverse
