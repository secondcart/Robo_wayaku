import Game.Metadata

open Set

World "Samarkand"
Level 1
Title "" -- "Bild/Urbild"



Introduction "
**アラプカ**: 私が長い間考えていることがいくつかあります。
もしかしたらあなたたちが助けてくれるかもしれません。例えば：…

彼女はあなたたちに命題を口述します。ロボがそれを書き留めます。
"

/---/
TheoremDoc Set.image_preimage_subset as "image_preimage_subset" in "Set"

namespace Set

Statement image_preimage_subset {A B : Type} (f : A → B) (T : Set B) :
    f '' (f ⁻¹' T) ⊆ T := by
  Hint "
    **ロボ**: ここの記法について説明する必要があると思います。
    明らかに写像 `f : A → B` が与えられています。
    部分集合 `S` の `A` に対する
    ```
    f '' S = \{f a | a ∈ S}
           = \{b | ∃ a ∈ S, f a = b}
    ```
    は `f` による像です。そして部分集合 `T` の `B` に対する
    ```
    f ⁻¹' T = \{ a | f a ∈ T}
    ```
    は `f` による原像です。"
/- This is literally true:
example : f '' S = { f a | a ∈ S} := by
  rfl

example : f ⁻¹' T = { a | f a ∈ T} := by
  rfl
--/
  Hint (hidden := true) "
    **ロボ:** 包含関係を示すには, 左辺から要素を取り出し, 右辺にあることを示します。
    まず `intro b` から始めてみましょう。
    "
  intro b
  intro hb
  Hint (hidden := true) "
    **ロボ**: 仮定 `{hb}` をより基本的な式に変換するには, `simp` を適用できます。
  "
  simp at hb
  obtain ⟨a, ha₁, ha₂⟩ := hb
  rw [ha₂] at ha₁
  assumption

NewDefinition Set.fimage Set.fpreimage

Conclusion "**アラプカ**: 素晴らしい。"
