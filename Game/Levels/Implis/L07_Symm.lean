import Game.Metadata

World "Implis"
Level 7

Title "Genau dann, wenn"

Introduction
"
**作戦責任者**: ここにもこんなものがあります. 
"

Statement (A B : Prop) (h : A ↔ B) : B ↔ A := by
  Hint "
    **あなた**: これはただ逆になっただけだ. 

    **Robo**: それ用のツールを知っています. `symm` または `symm at {h}` を使えば, どちらかを反転できます. "
  Branch
    symm at h
    assumption
  symm
  assumption

Conclusion
"
**作戦責任者**: これは簡単でしたね. でも次の問題はもっと難しそうです. 
"

NewTactic symm
DisabledTactic tauto
