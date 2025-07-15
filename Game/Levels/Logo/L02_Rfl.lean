import Game.Metadata

World "Logo"
Level 2

Title "千里の道も... 1行から?"

Introduction
"
その間に, 質問をしたい家臣たちの長い列がすでにできていました. Logisinde女王が最初の者を手招きします. 彼は咳払いをします.

**家臣** なぜ`42 = 42`なのですか?

あなたは呆然とした表情で彼を見ます.
彼は再びそれを書き留めます.
"

Statement :
  42 = 42 := by
  Hint "**Robo** それは明らかです. 等式が*反射的(reflexive)*であることを思い出させればいいのです. `rfl`を試してみてください.
    "
  rfl

Conclusion
"
**家臣** ああ, その通りです. はい, まったく正しいです. 私はいつもそれを忘れてしまいます. `rfl`, `rfl`, `rfl`…

# 今回学んだこと

## Tactics
### rfl
- `X=X` を証明します. 正確には, `A` と `B` が定義的に等しい場合に `A=B` を証明します.

## Definition
### `=`
- 等式. 有用なtacticとして, `rfl`, `rw`, `trans` がある.
"

NewDefinition Eq

NewTactic rfl
DisabledTactic tauto
