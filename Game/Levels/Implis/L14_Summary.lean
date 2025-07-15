import Game.Metadata

World "Implis"
Level 14

Title "まとめ"

Introduction
"
**作業責任者** 本当に助かりました! これが最後の問題です.
前任者から引き継いだもので, これを解決できれば全てがうまくいくと言っていました.
しかし私には難しすぎて挑戦する気にもなりませんでした. 試してみますか?

**あなた** もちろん見せて! Robo, ここまで5分間で学んだ理論的なことをまとめて表示してくれる?

**Robo** 概要はこちらです：

## 表記/用語

|     | 説明                     |
|:--- |:------------------------ |
| `→` | 含意                     |
| `↔` | 同値/必要十分条件        |

## tactic

| tactic       | 例                                                          |
|:--------------- |:---------------------------------------------------------- |
| `intro`         | 証明目標の含意の左辺を仮定に取り込む                       |
| `revert`        | `intro`の逆操作                                            |
| `apply`         | 含意を証明目標に「逆向き」に適用                           |
| `apply at`      | 含意を仮定に「順方向」に適用                               |
| `symm`          | `A ↔ B`を`B ↔ A`に変更                                     |
| `trans`         | `A ↔ C`を`A ↔ B`と`B ↔ C`に分割                           |
| `rw [h] `       | 同値`h`を使って証明目標を書き換え                          |
| `rw [h] at h₁`  | 同値`h`を使って仮定`h₁`を書き換え                          |
| `by_cases h : P`| `P`と`¬P`で場合分け                                        |                      |
"

/-- 多くの場合, `tauto`もこの種の論理式を解くことができます. -/
TheoremDoc imp_iff_or_not as "imp_iff_or_not" in "Logic"

/-- 多くの場合, `tauto`もこの種の論理式を解くことができます. -/
TheoremDoc imp_iff_not_or as "imp_iff_not_or" in "Logic"

set_option tactic.hygienic false

Statement imp_iff_not_or {A B : Prop} : (A → B) ↔ ¬ A ∨ B := by
  Hint "**あなた** *(小声)*: これって`→`の定義じゃない?

  **Robo** *(小声)*: そう見えるかも. でもLeanでは単なる同値です"
  constructor
  intro h
  Hint (hidden := true) "**Robo** また`by_cases`が使えるかも"
  Branch
    by_cases A


  by_cases hA : A
  apply h at hA
  right
  assumption
  left
  assumption
  Hint (hidden := true) "**Robo** 含意はいつも`intro`で攻めるんだ"
  intro h
  intro ha
  Branch
    by_cases ha : A
  Branch
    by_cases A
  Hint (hidden := true) "**Robo** 仮定`h`を`obtain`で分割してみたら? "
  obtain h | h :=  h
  contradiction
  assumption

DisabledTactic tauto

NewTheorem imp_iff_or_not

Conclusion "
**作業責任者** 素晴らしい! 本当にありがとう! もうこれ以上引き止めません.
Quantus星へ向かうんでしょう?

**あなた** ええ, 多分…

**作業責任者** 最後にお願いがあります. Quantusの女王様への小包が…
これも前任者から引き継いだものです. 住所が分からないので郵便局が引き取ってくれません.
届けてもらえませんか?

**あなた** もちろん! Robo, ちょっと.

Roboは小包を受け取り, 内部に消えさせた.
作業責任者は驚いた顔で見つめた.

**Robo** 心配ない, 私は何も消化しません!
"
