import Game.Metadata


World "Logo"
Level 9

Title "Aus Falschem folgt vieles."

Introduction
"
三番目の苦情者の登場。
"

/--  -/
Statement (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  Hint "
    **あなた** また仮定の中に矛盾があるの？

    **ロボ**: だんだんコツがわかってきたみたいだね"
  contradiction

Conclusion
"
**ロボ**: よくできました。この問題では, 矛盾がどこにあるのか少し明白でしたね:
仮定 `n ≠ 10` は `n = 10` の否定そのものです。
`≠` は常に `¬(· = ·)` と読む必要があります。
"

DisabledTactic tauto
