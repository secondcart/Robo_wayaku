import Game.Levels.Robotswana.L04_MatrixEqSum

World "Robotswana"
Level 5

Title "Einheitsmatrix"

Introduction
"
**あなた**: ちょっと見せて, 何を持ってるの？単位行列？私たちのコレクションにぴったりじゃない？

**Robo**: はい - 右端の`1`がここでは単位行列です。
  `matrix_eq_sum_ebasis`から始められると思います。

**あなた**: 広場に重要なものを置き忘れてないか気になるな...

**Robo**: どうでもいいよ, もうずいぶん先に進んでる。ここで試してみて！
"

Conclusion "**あなた**: 行列の対角線に興味がある誰かの跡を追ってる気がする。でも喉が渇いてきた！"


open Nat Matrix StdBasisMatrix

open Finset

    -- around Matrices/level 2: introduce E_ij-version of Matrix.StdBasisMatrix.mul_of_ne,
    -- prove it in one line via mathlib, and use it in level 7.
    -- Matrices/level 3, sum not displayed: already fixed in mathlib


-- -- Not used later on in our proofs, but possibly useful and can be safely
-- -- removed, or given as a hint
-- lemma tmp0 {n : ℕ} {i : Fin n} :
--     E i i = stdBasisMatrix i i ((1 : Mat[n,n][ℝ]) i i) := by
--   rw [one_apply]
--   unfold E
--   simp?

/---/
TheoremDoc Matrix.ebasis_diag_sum_eq_one as "ebasis_diag_sum_eq_one" in "Matrix"

Statement Matrix.ebasis_diag_sum_eq_one {n : ℕ} : ∑ i : Fin n, E i i = 1 := by
  Hint (hidden := true) "
    **Robo**: 言った通り, `matrix_eq_sum_ebasis`から始められると思うよ, 
    等号の右側の単位行列`1`に適用して。
    だから`matrix_eq_sum_ebasis 1`で目標を`r`e`w`riteしたいんだ。
  "
  Branch
    rw [matrix_eq_sum_std_basis 1]
    Hint "**Robo**: 違うよ, `matrix_eq_sum_std_basis`じゃなくて`matrix_eq_sum_ebasis`だよ。"
  rw [matrix_eq_sum_ebasis 1] -- Lvl 3
  Hint "**あなた**: 各項が同じだから, 2つの和は同じだと思う。"
  Hint (hidden := true) "
    **Robo**: それならまた`sum_congr`を使うべきかも。
  "
  apply sum_congr
  rfl
  intro i hi
  Hint "**あなた**: で, 次は？

  **Robo**: `funext r s`で行列の$(r,s)$成分に注目できるよ。"
  funext r s
  Hint "**あなた**: ここでの`1`は単位行列だよね？

  **Robo**: そうだよ。

  **あなた**: なら`1 {i} j`は`j ≠ {i}`なら全部0だ。
  だから`j = {i}`の項以外は消える。

  **Robo**: そうかな？考えさせて...
  まず`have h : \{{i}} ⊆ univ`を証明できる？"
  have h : {i} ⊆ univ
  · simp
  Hint "**Robo**: 良かった。これで`sum_subset`が使えるよ。"
  rw [← sum_subset h]
  · Hint "**あなた**: ありがとう, 助かる！このステップは簡単だ: 1要素の和で, 
    `1 {i} {i}`は1で, `1 • _`も簡約される！"
    Hint (hidden := true) "**Robo**: `simp`はいつでも試せる..."
    simp
  · intro x h₁ h₂
    clear h₁ -- not needed
    Hint "**あなた**: でもここはどうする？`{h₂}`はほぼ`{i} ≠ {x}`ってことだよね。

    **Robo**: そうだけど, 完全には。`have h₃ : {i} ≠ {x}`を導入して簡単に示して！"
    -- TODO: There are other ways to get `i ≠ x`!
    Branch
      have h₃ : x ≠ i
      Hint "**Robo**: 逆の方が有用だよ, 
      `1 {i} {x}`は`if {i} = {x} then _ else _`で定義されてるから！

      **あなた**: その通り, すぐ`{i} = {x}`か`{i} ≠ {x}`が必要だ。変えよう。"
    have h₃ : i ≠ x
    · Hint "**あなた**: まず`{h₂}`が簡約できるか見てみよう。"
      simp at h₂
      -- TODO : `tauto` already solves this.
      Hint "**あなた**: うーん, 今は逆だ。

      **Robo**: `symm`を思い出して！

      **あなた**: そうだった, あのベルトコンベアの変な人の時も使ったね。"
      symm
      assumption
    Branch
      simp [h₃]
    Hint "**あなた**: `1 {i} {x}`の定義はどう入れる？

    **Robo**: `Matrix.one_apply`！"
    rw [Matrix.one_apply]
    Hint "**Robo**: 間違ってるから, `rw`と`if_neg`で進めるよ。"
    rw [if_neg h₃]
    simp

/---/
TheoremDoc Matrix.one_apply as "one_apply" in "Matrix"

NewTheorem Matrix.one_apply

TheoremTab "Matrix"
