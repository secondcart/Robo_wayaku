import Game.Metadata

World "Implis"
Level 13

Title "補題の使用"

Introduction
"
**作戦責任者** また同僚のための仕事だ…. 彼はまた`apply`を使わない証明を求めてきた. ここには以前にメモした内容もあるな. そうだ, この補題がある:
```
lemma not_not (A : Prop) : ¬¬A ↔ A
```

**作戦責任者** これでできるかな?
"

Statement (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  Hint "
    **Robo** `not_not`のように`↔`や`=`を持つ補題は, `rw [not_not]`という形で使用できます. "
  rw [not_not]
  Hint "
    **あなた** え, なぜこれで`¬¬`の2つが書き換わったの?

    **Robo** `rw`は最初に見つけたものだけを書き換えるので, `¬¬C`が対象です. ただしこれは複数回出現するので, すべて置換されます…

    **あなた** ああ, `¬¬B`は別物だから, もう一度補題を使う必要があるんだね. "
  rw [not_not]

Conclusion
"
**あなた** もう終わったの…?

**Robo** はい, `rw`はその後自動で`rfl`を呼び出そうとしますが, 今回はそれが成功しました.
"

OnlyTactic rw


/-- この声明の代わりに, しばしば`tauto`や`simp`というtacticも使用可能です. -/
TheoremDoc Classical.not_not as "not_not" in "Logic"
NewTheorem Classical.not_not
TheoremTab "Logic"
