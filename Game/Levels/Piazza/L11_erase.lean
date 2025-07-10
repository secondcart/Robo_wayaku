import Game.Metadata

World "Piazza"
Level 11

Title ""

Introduction "
**Mem**: ねえ, Fin, 何してるの? 

Finはグループで一番小さく, 今まで何も話していませんでした. 
そして今, 隣の屋台からピスタチオを盗んだようです. 

**Fin**: ただの小さな練習だよ. 

**Mem**: どんな練習? 

Finは次のように説明します. 
"

open Set

Statement (A : Finset ℕ) (a : ℕ) : Finset.erase A a = A \ {a} := by
  Hint "
    **あなた**: ここでの`Finset`ってどういう意味? 

    **Robo**: これは`A`がℕの*有限*部分集合に属することを意味します. 
    でも質問には実は関係ありません. 
    左側には`a`のない`A`, 右側にも`a`のない`A`があります. 
    "
  ext
  simp
  tauto

TheoremTab "Set"

Conclusion ""

NewDefinition Finset.erase
