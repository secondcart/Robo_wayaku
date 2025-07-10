import Game.Metadata

World "Iso"
Level 1
Title "Bijektivität"

Introduction
"
**イソソソフ**: もちろん, 私たちもあなたたちのために準備しておきました. 
"

open Function

Statement :
    let f := fun (n : ℤ) ↦ n + 1
    Bijective f := by
  Hint "
    **Robo** *(小声で)*: `Bijective f` は `Injective f ∧ Surjective f` と定義されています. 

    **あなた**: それならとても簡単ですね! "
  unfold Bijective
  constructor
  · intro a b hab
    simp [f] at hab
    assumption
  · intro y
    use y-1
    simp [f]

NewDefinition Function.Bijective
TheoremTab "Function"

Conclusion
"
**イソソソフ**: 素晴らしい. それなら, ここは全部飛ばしてもいいと思います…

彼は数枚の紙を脇に置いた. 
"
