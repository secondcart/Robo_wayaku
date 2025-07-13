import Game.Levels.Robotswana.L03

World "Robotswana"
Level 4

Title "Summe von Basiselementen"

Introduction "あなたたちは, より大きな正方形のエリアで草が踏み荒らされている場所に到着しました. 跡はあちこちに, さまざまな方向へと続いています.

少し当てずっぽうにその場所を探すと, 様々な羊皮紙の破片が見つかります. ほとんどは空白か判読不能ですが, 1つだけ解読できるものがありました. "

Conclusion "
あなたは特に目立つ跡を追うことに決めました. Roboが後をついてきて, 歩きながら地面から適当な羊皮紙の破片を拾います.
"

open Nat Matrix StdBasisMatrix -- BigOperators

/-- 任意の$(n × n)$行列（$\mathbb{R}$上）$A$は, $A = \sum_{i=0}^{n-1}\sum_{j=0}^{n-1} A_{ij} \cdot E(i, j)$と書けることを述べています.

また, $(m × n)$行列（任意の環$R$上）に対する一般化された形式である`matrix_eq_sum_std_basis`も参照してください. -/
TheoremDoc Matrix.matrix_eq_sum_ebasis as "matrix_eq_sum_ebasis" in "Matrix"

Statement Matrix.matrix_eq_sum_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) :
    A = ∑ i : Fin n, ∑ j : Fin n, (A i j) • E i j := by
  Hint "**あなた**: これは単にこれらの`E i j`が行列の空間の生成系をなすと言っているように見えます.

    **Robo**: きっと既に見つけた結果をすぐに適用できるでしょう! "
  Hint (hidden := true) "**Robo**: まず式`(A i j) • E i j`を見てください. 和の下では`simp_rw`が必要です. "
  Branch
    unfold E
    Hint "**Robo**: そうですね, 最初の羊皮紙の証明を単に繰り返すこともできます.
    どうぞ, 習うより慣れろです.

    **あなた**: 分かったよ, 私はあなたのような機械的な頭脳を持っていないから. "
    simp
  simp [Matrix.smul_ebasis] -- Lvl 1
  Hint "**Robo**: ああそうだ! 今ここにあるように, この主張は私のライブラリから知っています.
  これはまさに`apply matrix_eq_sum_std_basis`です.

  **あなた**: すごい! じゃあ私たちはこれに時間を費やす必要はないですね. "
  apply matrix_eq_sum_std_basis

/-- `matrix_eq_sum_ebasis`のより一般的なバージョンです. そちらを参照してください. -/
TheoremDoc Matrix.matrix_eq_sum_std_basis as "matrix_eq_sum_std_basis" in "Matrix"
NewTheorem Matrix.matrix_eq_sum_std_basis

TheoremTab "Matrix"
