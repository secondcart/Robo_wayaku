import Game.Metadata


World "Epo"
Level 7

Title ""

Introduction ""

open Set

/---/
TheoremDoc Function.surjective_iff_hasRightInverse as "surjective_iff_hasRightInverse" in "Function"

namespace Function

Statement surjective_iff_hasRightInverse {A B : Type} (f : A → B) :
    Surjective f ↔ HasRightInverse f := by
  constructor
  · intro hs
    choose g hg using hs
    -- unfold HasRightInverse
    use g
    assumption
  · -- this is `Function.HasRightInverse.surjective`
    intro ⟨g, inv⟩
    intro b
    use g b
    apply inv

TheoremTab "Function"

Conclusion "
皆さんには大きな拍手が送られます。

その後, お別れの挨拶があります。
残念ながら帰り道は輸送カプセルを使えません。
なぜならそれらは片方向にしか機能しないからです。
宇宙船へ戻るには徒歩で行くことになります：まず階段を下り, オフィスビルから睡眠塔へ外に出て, 最後に普通のエレベーターで上へ上がります。
"
