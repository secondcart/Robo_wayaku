import Game.Metadata

World "Babylon"
Level 1

Title ""

Introduction
"
**バビロニア人**: 各塔には碑文があります. そこに, なぜその塔が建てられたのかを詳しく読むことができます. 例えば, ここにあります. 
"

open Nat Finset
Statement (I : Finset ℕ) : (∑ i ∈ I, 1) = card I := by
  Hint "
    **あなた**: ああ, これは本当にたくさんの新しいことだ…見てみよう…

    これは $( \\sum_\{i\\in I} 1)$ が…に等しいように見えます. 

    **Robo**: …$I$の要素の数, つまり$I$のカーディナリティです. 

    **バビロニア人**: そして, これを証明できますか？

    **Robo** *(あなたに向かって)*: 最初に`simp`を試してみることをお勧めします. 
    これは本当に強力な戦術で, 多くの項を単純化します. "
  simp

TheoremTab "∑ Π"

Conclusion "**バビロニア人**: よくできました, これで合っています！"

NewDefinition Finset.card

/-
**Robo**: Mir fällt gerade ein, du hattest ja mal gefragt bezüglich `rw` unter Quantoren.
Mit Summen ist das das gleiche: Hier musst du immer `simp_rw` verwenden, wenn du innerhalb
einer Summe was umschreiben möchtest."
-/
