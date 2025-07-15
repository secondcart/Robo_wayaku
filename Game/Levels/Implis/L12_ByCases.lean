import Game.Metadata

World "Implis"
Level 12

Title "by_cases"

Introduction
"
次の問題に取り組んでいると, 作戦責任者は考え込んだ.

**作戦責任者** 正直なところ, この書類がどこから来たのか分からない. 私のものではないんだが,
なんだか面白そうだ.
"

Statement (A : Prop) : ¬A ∨ A := by
  Hint (strict := true) "
    **あなた** まあ, `A`か`¬A`のどちらかは真になるでしょう.

    **Robo** これは場合分けの典型的なケースだね. `by_cases h : A`を試してみて. "
  by_cases h : A
  Hint "
    **Robo** ほら, 証明が2つの部分に分かれたでしょう. 最初の部分では`A`が真だと仮定して,
    2番目の部分では`A`が偽だと仮定するんだ. "
  right
  assumption
  left
  assumption

Conclusion
"
作戦責任者は納得して頷いた.
"

NewTactic by_cases
DisabledTactic tauto
