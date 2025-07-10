import Game.Metadata

World "Piazza"
Level 3

Title ""

Introduction
"
  **集合**: もしこれが簡単すぎたなら——この発言を知っていますか？
"

open Set

Statement (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  Hint "
    **あなた**:  `A B C : Set ℕ` ここでは正確には何を意味する？

    **Robo**:  それは単に, `A`, `B`, `C` が `ℕ` の*部分集合*であることを意味します。

    **あなた**:  `Set` は「部分集合」という意味？

    **Robo**:  そう言ってもいいでしょう, はい。

    **あなた**:  それなら, この主張は*知っている*かもしれません。
    でも, どうやってここで証明できるかは全くわかりません。

    **Ext**:  私が教えられます！魔法の言葉があります, それは私と全く同じ名前です！！

    **Robo**:  ああ, そうですね——
    `ext x` は集合の等式 `A = B` を `x ∈ A ↔ x ∈ B` に置き換えます。"
  ext x
  Hint "**Robo**:  そして今度も `simp` です。"
  simp -- simp only [mem_inter_iff, mem_union]
  Hint "
    **あなた**:  `simp` は実際には何をしているのですか？

    **Robo**:  `simp` は一般的に知られている等式や同値関係を探し, 
    一般的に簡略化と見なされ, 現在適用可能なものを探します。
    `simp` が見つけたすべての簡略化を適用します。
    今まさに, 例えば次の形式の簡略化がありました：
    ```
    {x} ∈ {A} ∩ {B} ↔ {x} ∈ {A} ∧ {x} ∈ {B}
    ```
    そして
    ```
    {x} ∈ {B} ∪ {C} ↔ {x} ∈ {B} ∨ {x} ∈ {C}.
    ```
  "
  Hint (hidden := true)"
    **Robo**:  残りはきっと `tauto` でできます。
  "
  tauto

NewTactic ext
NewDefinition Set.union Set.inter
TheoremTab "Set"

Conclusion ""
