import Game.Metadata


World "Logo"
Level 8

Title "Aus Falschem folgt vieles."

Introduction
"
2番目の反逆者の登場. 
"

/--  -/
Statement (n : ℕ) (h : n ≠ n) : n = 37 := by
  Hint "
    **あなた**: `{n} ≠ {n}`も矛盾してるんじゃない? 

    **Robo**: 試してみて！"
  contradiction

Conclusion
"
**あなた**: うん, うまくいったみたい. 

**あなた**: でもまだちょっと怪しい気がする. 
任意の自然数が37に等しいことを証明しちゃった? 

**Robo**: いやいや, そうじゃない. 自分自身と等しくない任意の数が37に等しいってこと. 
そして38にも, 39にも, …

**あなた**: わかったわかった, 理解したよ. 
"

NewDefinition Ne
DisabledTactic tauto
