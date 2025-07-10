import Game.Metadata

World "Logo"
Level 2

Title "Aller Anfang ist... ein Einzeiler?"

Introduction
"
その間に, 質問をしたい臣下たちの長い列がすでにできていました. ロジシンデが最初の者を手招きします. 彼は咳払いをします. 

**臣下**: なぜ`42 = 42`なのですか? 

あなたは呆然とした表情で彼を見ます. 
彼は再びそれを書き留めます. 
"

Statement :
  42 = 42 := by
  Hint "**Robo**: それは明らかです. 等式が*反射的*であることを思い出させればいいのです. `rfl`を試してみてください. 
    "
  rfl

Conclusion
"
**臣下**: ああ, その通りです. はい, まったく正しいです. 私はいつもそれを忘れてしまいます. `rfl`, `rfl`, `rfl`…
"

NewDefinition Eq

NewTactic rfl
DisabledTactic tauto
