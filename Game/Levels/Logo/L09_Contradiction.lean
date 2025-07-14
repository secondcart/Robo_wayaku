import Game.Metadata


World "Logo"
Level 9

Title "矛盾からはなんでも導ける3"

Introduction
"
3人目の曲者の登場.
"

/--  -/
Statement (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  Hint "
    **あなた** また仮定の中に矛盾があるの?

    **Robo** だんだんコツがわかってきたみたいだね"
  contradiction

Conclusion
"
**Robo** よくできました. この問題では, 矛盾がどこにあるのか少しわかりやすかったですね.
仮定 `n ≠ 10` は `n = 10` の否定そのものです.
`≠` は常に `¬(· = ·)` と読む必要があります.
"

DisabledTactic tauto
