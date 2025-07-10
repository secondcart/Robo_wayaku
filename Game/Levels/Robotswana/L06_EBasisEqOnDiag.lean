import Game.Levels.Robotswana.L05_EBasisDiagSum

World "Robotswana"
Level 6

Title "Ein nihilierter Kommutator"

-- TODO: Intro & geschichte
Introduction
"
足跡をたどると大きな木の前に到着しました. 木陰で動かない何かを見つけます：

$$
[A, B] = AB - BA
$$

**Robo**: ああ, 交換子だね! 

**あなた**: でもかなり無効化されているみたい. 干からびてるんじゃない? 

**Robo**: 見て, 木に何か書き込まれているよ. 
"


Conclusion "
**Robo**: 交換子が無効化されるという仮定は, ひとまず受け入れることにしましょう. 

**あなた**: いいね. のどが渇いてきたって言ったっけ? 
"

open Nat Matrix

/---/
TheoremDoc Matrix.eq_on_diag_ebasis as "eq_on_diag_ebasis" in "Matrix"

Statement Matrix.eq_on_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))  :
    ∀ (i j : Fin n), f (E i i) = f (E j j) := by
  Hint "**あなた**: つまり, `f`が交換子を無効化するなら, すべての`E i i`での値は一致するってこと? 合ってる? 

  **Robo**: 確かめてみよう! "
  intro i j
  Branch
    Hint "**あなた**: でも仮定`{h₁}`をどう使えばいいの? まず行列積が必要だ. 

    **Robo**: `f (E i i) = f (A * B) = f (E j j)`となる行列積`A * B`を見つける必要があるね. 
    そうすれば`trans f (A * B)`と書いて, `f (E i i) = f (A * B)`と`f (A * B) = f (E j j)`の2つの証明目標に分けられる. 
    `{h₁}`が使えるかもしれない. "
    Hint (hidden := true) "**Robo**: `E i k = (E i j) * (E j k)`ってメモに書いてなかった? "
    trans f (E i j * E j i)
    · unfold E
      simp
    · Hint (hidden := true) "**Robo**: `{h₁}`を使いたかったからこれをやってたんじゃない? 

      **あなた**: あ, そうだった! "
      rw [h₁]
      unfold E
      simp
  specialize h₁ (E i j) (E j i)
  simp [E.mul_same] at h₁
  assumption

TheoremTab "Matrix"
