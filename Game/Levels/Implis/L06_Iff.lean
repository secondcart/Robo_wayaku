import Game.Metadata

World "Implis"
Level 6

Title "Genau dann, wenn"

Introduction
"
**オペレーションマネージャー**: 私たちは以前, 両方向に動くことができるいくつかのコンベアベルトを持っていました. 最新のマニュアルではこのようなダブルベルトは推奨されていないため, 念のためすべて停止させていました. しかし特定の条件下では安全かもしれませんね? この件についてどう思いますか? 
"

Statement (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  Hint "
    **Robo**: `A ↔ B` はもちろんLeanでの $A \\iff B$, つまり「ちょうどそのとき」を表します. 
    この命題 `A ↔ B` は2つの部分から成り立ち, `⟨A → B, B → A⟩` と定義されます. 

    **あなた**: つまりANDの `A ∧ B` とよく似ているんですね? 

    **Robo**: その通りです. したがって, ここでも `constructor` から始めることができます. "
  constructor
  Hint "**あなた**: ああ, そしてその2つの部分はすでに前提条件にありますね. "
  assumption
  assumption

Conclusion
"
**オペレーションマネージャー**: わかりました, 納得です. 

**Robo** *(あなたに向かって)*: ところで, `(h : A ∧ B)` の2つの部分が `h.left` と `h.right` と呼ばれるように, 
`(h : A ↔ B)` の2つの部分は `h.mp` と `h.mpr` と呼ばれます. 

**あなた**: つまり `h.mp` は `A → B` ですか? なぜ `mp` なんですか? 

**Robo**: `mp` はモーダスポネンスを表します. モーダスポネンスは古代論理学で既に知られていた推論規則で, 多くの論理システムで...あ, いえ, それは聞きたくなかったですよね. 「mpr」の「r」は「reverse」を意味し, 逆方向だからです. 
"

NewDefinition Iff
DisabledTactic tauto rw
