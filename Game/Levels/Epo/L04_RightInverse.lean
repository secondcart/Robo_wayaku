import Game.Metadata


World "Epo"
Level 4

Title ""

Introduction ""

open Function

-- in mathlib: `Function.rightInverse_iff_comp`
Statement {A B : Type} {f : A -> B} {g : B -> A} :
    RightInverse g f ↔ f ∘ g = id := by
  Hint "
  **あなた**: そろそろ定義を少しずつ確認していく必要がありそうですね? 

  **Robo**: そのようです. "
  Hint (hidden := true) "
  **Robo**: 実際, また`constructor`から始めるのが良いでしょう. 
  そして`comp_apply`, `congr_fun`などお馴染みのものを使うと良いです. "
  constructor
  · intro h
    funext x
    Branch
      rw [comp_apply]
      rw [h x]
      rw [id_eq]
    apply h
  · Branch
      apply congr_fun
      done
    intro h
    intro x
    Hint (hidden := true) "
    **Robo**: `apply congr_fun at h` または `rw [← comp_apply (f:= f)]`を使ってみてはどうでしょう. 
    (`rw [← comp_apply]`だけではここでは機能しません
    - `comp_apply`の命題において変数`f`がどの値を持つかを明示的に指定する必要があります. "
    Branch
      rw [← comp_apply (f:= f)]
      rw [h]
      rfl
    apply congr_fun at h
    apply h

TheoremTab "Function"
