import Game.Levels.Samarkand.L07_LeftInvPreimage

World "Samarkand"
Level 8

Title "Preimage of surjective is injective"

Introduction "
  **Arapuka**: この予想について, さらに助けてもらえるでしょうか? 
"

open Function

/---/
TheoremDoc Set.preimage_injective as "preimage_injective" in "Function"

namespace Set

Statement preimage_injective {A B : Type} {f : A → B} : Injective (preimage f) ↔ Surjective f := by
  Hint "
    **Robo**: 写像が全射であることと, 部分集合をその部分集合の下での原像に送る誘導写像`preimage f`が単射であることは同値ですか? 
    これは本当に正しいのでしょうか? 

    **あなた**: そうだと思います. 以前見たことがあります. 

    **Robo**: それでは, 始めましょう! 
  "
  constructor
  · Branch
      intro h_inj
      intro b
      by_contra h_contra
      push_neg at h_contra
      have h : preimage f {b} = ∅ := by
        rw [eq_empty_iff_forall_not_mem]
        intro a
        specialize h_contra a
        assumption
      have : preimage f ∅ = preimage f {b}
      rw [preimage_empty,h]
      apply h_inj at this
      symm at this
      rw [eq_empty_iff_forall_not_mem] at this
      apply this b
      simp
    intro hinj y
    have h : f ⁻¹' {y} ≠ ∅ ↔ (∃ a, f a = y) := by -- see L06_PreimageNonempty
      unfold Ne
      rw [eq_empty_iff_forall_not_mem]
      simp
    rw [← h]
    -- change f ⁻¹' {y} ≠ ∅ -- TODO: it's displayed not nicely :(
    have g : f ⁻¹' ∅ = ∅ := by
      simp
    rw [← g]
    -- or: `rw [← preimage_empty]`
    rw [Injective.ne_iff hinj]
    simp
  · intro h_surj
    intro s s' hs
    apply congr_arg (image f) at hs
    rw [Surjective.image_preimage h_surj] at hs
    rw [Surjective.image_preimage h_surj] at hs
    assumption

Conclusion "
  **Arapuka**: 素晴らしい!  興奮して飛び上がりたい気分です. 
  しかしもちろんそれはできません. そうするとパターンが台無しになってしまいます. 

  **Robo**: あとどれくらい時間があるのですか? 

  **Arapuka**: ここにあと3年と22日7時間35分です. 

  **Robo**: ああ…

  **あなた**: そして, パターンが合うようにその後どこに行けばいいのか, どうやって知るのですか? 

  **Arapuka**: ああ! 

  Arapukaの顔に大きな笑みが広がります. 

  **Arapuka**: それがまさに芸術なのです! 
"
