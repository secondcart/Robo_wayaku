import Game.Levels.Robotswana.L06_EBasisEqOnDiag

World "Robotswana"
Level 7

Title "Desinteresse"

Introduction
"
木のすぐ横に、大きく`E i j`と書かれたメモが線で消されているのを見つけました。

**あなた**: つまり、i ≠ jの場合の`E i j`は興味がないということでしょう。

"

Conclusion "足跡はますます新鮮に見え、あなたは以前よりも速く、そして無防備にそれらを追いかけています。"

open Nat Matrix StdBasisMatrix

/---/
TheoremDoc Matrix.zero_on_offDiag_ebasis as "zero_on_offDiag_ebasis" in "Matrix"

Statement Matrix.zero_on_offDiag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) :
    ∀ (i j : Fin n ), (i ≠ j) → f (E i j) = 0 := by
  intro i j hne
  Branch
    rw [← E.mul_same i j j]
    rw [h₁]
    rw [E.mul_of_ne] -- (***)
    -- The first goal and its associated proof state
    -- at this point of a correct solution
    -- match the first goal and proof state
    -- of an incorrect attempt further below!
  Branch
    Hint "**ロボ**: ここで`{h₁}`をどう使えるでしょうか？

    **あなた**: 今回は`E i j`を積`E i j * E j j`と書いてみたらどうでしょう？

    **ロボ**: なぜそうするのですか？

    **あなた**: この積で因子を入れ替えるとゼロになります！`E.mul_of_ne`のようなものでしたよね。"
    Hint (hidden := true) "**ロボ**: そうですか。では`trans f (E i j * E j j)`を試してみてください。"
    trans f (E i j * E j j)
    · Hint (hidden := true) "**あなた**: ええと、これは定義から明らかです。

      **ロボ**: `unfold E`を忘れずに、または`E`の定義を使用するように`simp`に伝えてください(`simp [E]`)。"
      simp [E]
    · Hint "**ロボ**: ここで可換にしたいのですか？

      **あなた**: その通りです！"
      Branch
        rw [E.mul_of_ne] -- (***)
        -- Would ideally like to already trigger a warning here, but
        -- first goal and proof state are identical to first proof
        -- reached in a correct solution (see (***) in first Branch above)
        simp
        Hint "**ロボ**: おや。これは間違っているようです。"
      rw [h₁]
      rw [E.mul_of_ne] -- Lvl 2
      · simp
      · symm
        assumption
  specialize h₁ (E i j) (E j j)
  simp [E.mul_same, E.mul_of_ne _ _ hne] at h₁
  simp [E.mul_of_ne _ _ hne.symm] at h₁
  assumption




NewTheorem Matrix.E.mul_of_ne
TheoremTab "Matrix"
