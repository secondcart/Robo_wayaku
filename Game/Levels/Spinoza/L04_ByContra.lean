import Game.Metadata
import Game.Levels.Implis -- to make sure `rw` doc is imported

World "Spinoza"
Level 4

Title ""

Introduction
"
**Benedictus** 奇数の二乗についての素敵な質問がまだあります.
しかしその前に, まずこの同値性を証明してください. これはあなた方の間では
*対偶の同値性*と呼ばれているのではないでしょうか? Leanでは単に
`not_imp_not`と呼んでいます. こちらの方がずっと分かりやすいですよね?
"
/---/
TheoremDoc not_imp_not as "not_imp_not" in "Logic"

Statement not_imp_not (A B : Prop) : A → B ↔ (¬ B → ¬ A) := by
  Hint "
    **あなた** はい, 確かにこれは以前見たことがあります.

    **Robo** もちろん見たことあるでしょう. 数学者はこれを頻繁に使います.
    $A ⇒ B$について何も思いつかない時は, 代わりに$¬B ⇒ ¬A$を示します. 私はこれを
    *対偶*ではなく*背中から胸を突き抜けて目に当てる*と呼びたいところです.
    しかしここではもちろん`not_imp_not`と呼ばれています. "
  Hint (hidden := true) "**Robo** `constructor`から始めてみてはどうでしょう. "
  constructor
  intro h b
  by_contra a
  Hint "**Robo** 再び`suffices g : B`を使って矛盾を導くのが良いでしょう. "
  suffices b : B
  contradiction
  apply h
  assumption
  intro h a
  Hint "**Robo** ここでも矛盾による証明を始めるのが良いでしょう. "
  by_contra b
  Hint (hidden := true) "**Robo** `suffices g : ¬ A`が良さそうです. "
  suffices g : ¬ A
  contradiction
  apply h
  assumption

Conclusion ""

DisabledTactic rw tauto
DisabledTheorem Classical.not_not
TheoremTab "Logic"
