import Game.Metadata

World "Epo"
Level 1

Title ""

Introduction "
移動は実際に短く, 苦痛もありません。
そして実際に盛大な歓迎が準備されています。
最初の興奮が収まった後, ここでも課題に直面することになります。"

open Function

Statement :
    let f := fun (n : ℤ) ↦ n + 1
    Surjective f := by
  Hint "**あなた**: `Surjective f`の定義は`∀ y, (∃ x, f x = y)`だと推測していますが, 正しいでしょうか？

  **ロボット**: そうだと思います。`unfold Surjective`で中身を見ることができます。必ずしも必要ではありませんが。"
  unfold Surjective
  intro y
  use y-1
  Branch
    simp [f]
  ring

/--
`Surjective f` bedeutet naheliegenderweise, dass die Abbildung `f` surjektiv ist.
Mit `unfold Surjective` (bzw. `unfold Surjective at h`) kann man leicht nachsehen, was das
in Quantorenschreibweise konkret bedeutet.
-/
DefinitionDoc Function.Surjective as "Surjective"
NewDefinition Function.Surjective
TheoremTab "Function"

Conclusion ""
