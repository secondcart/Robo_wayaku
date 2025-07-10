import Game.Metadata

World "Babylon"
Level 4

Title ""

Introduction
"
  あなたは塔から塔へとさらに歩き続けます。ついに、奇妙に感じる塔の前で立ち止まりました。一周してみると、その理由がわかります：
  入口がありません。しかし、次のような碑文が刻まれた床板を見つけました。
"

open Finset

Statement  (n : ℕ) (hn : 3 ≤ n) : ∑ i ∈ Icc 0 n, (i^3 - 3 * i^2 + 2*i : ℤ ) = ∑ i ∈ Icc 3 n, (i^3 - 3*i^2 + 2*i : ℤ) := by
  Hint "**あなた**: ゆっくりいこう。示すべきは：

  $$
  \\sum_\{i=0}^\{n} (i^3 - 3 i^2 + 2 i)  = \\sum_\{i=3}^\{n} (i^3 - 3 i^2 + 2i)
  $$

  おそらく、和の中の式は最初の3つのiの値に対して単に0になる…そう、その通りだ。
  では、これをどう表現すればいい？

  **ロボ**: `sum_subset`を使うといいよ：`I₁ ⊆ I₂`で、
  和の中の式が`I₁`の要素で`I₂`に含まれないすべての要素に対して0になるなら、
  `I₁`の和は`I₂`の和に等しい。
  "
  Branch
    apply sum_subset
    Hint "**ロボ**: いや、それは逆に見えるね。"
    Hint (hidden := true) "**ロボ**: まず`symm`で等式の両辺を入れ替えて。"
  symm
  Hint (hidden := true) "**ロボ**: いいね。そして`apply sum_subset`。"
  apply sum_subset
  Hint "
    **ロボ**: ここでは`Icc_subset_Icc_iff`が役立つはずだよ。
  "
  · rw [Icc_subset_Icc_iff] -- introduced in PIAZZA
    · omega
    · assumption
  · -- showing that x = 0 or 1 or 2:  see Luna L??
    Hint "
      **ロボ**: 素晴らしい！あとはさっき言ったことを示すだけ：
      和の下の式は最初の3つのインデックスで0になる。"
    Hint (hidden := true)"
      **ロボ**: まずすべての仮定を導入して、
      ```
         i ^ 3 - 3 * i ^ 2 + 2 * i = 0
      ```
      が証明目標になるまで進めることを提案するよ。
    "
    Branch
      simp
      intro i h0 h3
      Hint "**ロボ**: 仮定から${i}=0$または${i}=1$または${i}=2$が導かれるはず。
    おそらく`have`で明示的に表現してみて。"
    intro i h0 h3
    Hint "**ロボ**: 仮定から${i}=0$または${i}=1$または${i}=2$が導かれるはず。
    `have`で明示的に表現してみて。"
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by
      Hint (hidden := true) "
        **ロボ**: 何らかの`simp`と`omega`の組み合わせで解決するはず。
        ルナでもうまくいったよ。
      "
      simp at h0 h3
      omega
    Hint (hidden := true) "
      **ロボ**: 仮定{h}を`obtain h | h | h  := {h}`で3つのケースに分けられるよ。
    "
    obtain h | h | h  := h
    · rw [h]
      ring
    · rw [h]
      ring
    · rw [h]
      ring

/---/
TheoremDoc Finset.sum_subset as "sum_subset" in "∑ Π"
NewTheorem Finset.sum_subset

TheoremTab "∑ Π"
