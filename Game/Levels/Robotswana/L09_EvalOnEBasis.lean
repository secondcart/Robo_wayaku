import Game.Levels.Robotswana.L08_EvalOnEBasis

World "Robotswana"
Level 9

Title "" -- "Matrix"

Introduction
"
50メートルも進まないうちに, 小さな丘に到着しました。
ロボが遠くの一点を指さします。

**ロボ**: 見て, あそこにあるよ！

**あなた**: それって何なの???

**ロボ**: わからない。でも私の直感では, これらの紙は一種のプロフィールみたいなものだと思う。ほら, ここにもう一枚ある。これには大きさが書いてあると思うよ。
"

Conclusion "
  **あなた**: わかった。慎重に近づいてみよう。
"

open Nat Matrix StdBasisMatrix Finset
-- Finset needs to be opened so that sum_congr is available
-- (not included in solution below, but can be used in alternative solutions)

/---/
TheoremDoc Matrix.one_on_diag_ebasis as "one_on_diag_ebasis" in "Matrix"

-- set_option trace.Meta.synthInstance true in
-- set_option pp.explicit true in

Statement Matrix.one_on_diag_ebasis {n : ℕ} (hn : n > 0) {f : Mat[n, n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    ∀ i, f (E i i) = 1 := by
  intro i
  Hint "
   あなたは少し考え込み, 紙に落書きを始めます。しばらくして：

   **あなた**: 考えが浮かんだよ！この`{n}`倍の式は, 以前の結果を使って次のように計算できると思う：
  $$
    \\begin\{aligned}
    n \\cdot f(E_\{i i})
    &= \\sum_j f(E_\{i i}) \\\\
    &= \\sum_j f(E_\{j j}) \\\\
    &= f(1) \\\\
    &= n
    \\end\{aligned}
  $$

  重要なポイントは, 任意の`i`と`j`に対して`f E i i`と`f E j j`が等しいことがわかっていることです。つまり, 総和の中で交換可能です。

  **ロボ**: うーん。とにかくまずは`{n}`を掛ける操作が単射であることを利用したいんだね？
     それに関する補題があったんじゃない？うーん…

  ロボはしばらく考え込む。

  **ロボ**: こうやってみたらどうかな：
     ```
     suffices h : n * f (E i i) = n * 1
     ```
  そして`mul_eq_mul_left_iff`で進める。
  "
  -- apply nat_mul_inj' (n := n)
  -- BEGIN new alternative (cf. Prado)
  suffices h : n * f (E i i) = n * 1 by
    rw [mul_eq_mul_left_iff] at h
    obtain h | h := h
    · assumption
    · Hint  "
      **ロボ**: `{hn} : {n} > 0`と`{h} : n = 0`では, `omega`が矛盾を見つけられるはずだよ。
      でも`{h}`にはℕからℝへの暗黙の埋め込みが含まれているかもしれない。
      念のためまず`simp at {h}`と書いてみて。
      "
      simp at h
      omega
  -- END
  Hint (hidden := true) "
  **ロボ**: 君の考えを正しく理解しているなら, 今は複数回`trans`を適用したいんだね, 最初に
  `trans ∑ j : Fin {n}, f (E i i)`として。
  "
  Branch
    rw [←smul_eq_mul, ← LinearMap.map_smul]
    Hint "**ロボ**: あれ, これはさっき書いたのと違うね。
      でもこれでもうまくいくかも。
      次は`trans {f} (∑ j : Fin {n}, E {i} {i})`としてみて。"
    trans f (∑ x : Fin n, E i i)
    · Hint "**あなた**: そう, この最初の等式では定数の総和を計算するだけだよ。

      **ロボ**: `simp [E]`で完全に簡約できるはずだよ。" -- TODO: Better hint
      simp [E] -- TODO: This is a bit magical in the sense that `simp; unfold E; simp` seems not to work
    · Hint (hidden := true )"**あなた**: 次に, 関数を総和の中に入れよう。"
      Hint "**あなた**: そして今度は, 中間ステップとして
      `{f} (∑ x, E x x)`を通じて等式を示したい。"
      trans f (∑ x, E x x)
      · Branch
          apply congr_arg
          Hint "**あなた**: いや, これは数学的に間違ってる！"
        Hint (hidden := true) "**ロボ**: 今度は`congr`-`ext`？

        **あなた**: いや, まず関数を総和の中に入れないとダメだよ。"
        rw [map_sum]
        Hint "**あなた**: もう一度！"
        rw [map_sum]
        apply congr_arg
        ext j
        Hint "**あなた**: これは私たちが途中で見つけた結果だよ。"
        Hint (hidden := true) "**ロボ**: 私の記憶装置によると`eq_on_diag_ebasis`だ。"
        rw [eq_on_diag_ebasis] -- Lvl 5
        assumption
      · Hint (hidden := true) "**ロボ**: これは`ebasis_diag_sum_eq_one`みたいだね。"
        rw [ebasis_diag_sum_eq_one] -- Lvl 4
        rw [h₂]
        simp
  · trans ∑ j : Fin n, f (E i i)
    · simp
    · trans ∑ j : Fin n, f (E j j )
      · apply congr_arg
        ext
        Hint (hidden := true) "**ロボ**: これはもう見たね。"
        rw [eq_on_diag_ebasis] -- Lvl 5
        assumption
      · trans f 1
        · Hint (hidden := true) "**ロボ**: ここで使いたかった結果は`eq_sum_apply_diag_ebasis`だったね。"
          rw [eq_sum_apply_diag_ebasis] -- Lvl 8
          · simp
          · assumption
        · Hint (hidden := true) "**ロボ**: `rw [{h₂}]`を試してみて。"
          rw [h₂]
          simp
  -- · simp -- previously needed for `nat_mul_inj'`



-- TODO: Each of the following theorems should ideally be introduced earlier!

/---/
TheoremDoc smul_eq_mul as "smul_eq_mul" in "Matrix"

/---/
TheoremDoc LinearMap.map_smul as "LinearMap.map_smul" in "Matrix"

--  TheoremDoc nat_mul_inj' as "nat_mul_inj'" in "ℕ"

/---/
TheoremDoc Nat.cast_eq_zero as "cast_eq_zero" in "ℕ"

TheoremTab "Matrix"
NewTheorem smul_eq_mul LinearMap.map_smul Nat.cast_eq_zero
--nat_mul_inj'
