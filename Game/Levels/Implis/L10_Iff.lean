import Game.Metadata

World "Implis"
Level 10

Title "Genau dann wenn"

Introduction
"
**作戦責任者**: これはまた私の理解の遅れた同僚のためです. 彼は`rw`も好きではないようです. それでもできますか? 
"

Statement (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  Hint "
    **あなた**: まあ, とりあえず`intro`から始められるかな…

    **Robo**: …そしてその後どうなるか見てみましょう！"
  intro hA
  Hint "
    **Robo**: つまり, 含意は`apply`で適用できます…

    **あなた**: 知ってるよ！でも`{h}`は含意ではなく同値です. 
    本当は`rw [← {h}]`と言いたいところです. 

    **Robo**: `{h}`の`{A} → {B}`方向は`{h}.mp`と呼ばれます. `apply ({h}.mp) at …`で適用できます. "
  Branch
    apply g
    Hint "**Robo**: もちろん, このように始めることもできます. "
    apply h.mp
    assumption
  apply h.mp at hA
  apply g at hA
  assumption

Conclusion "
**作戦責任者**: はい, 素晴らしい. これでうまくいくはずです. 

彼はまた電話しています. 

**作戦責任者**: ビンゴ！
"

DisabledTactic tauto rw
