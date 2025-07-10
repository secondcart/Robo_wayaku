import Game.Levels.Robotswana.L07_EBasisZeroOffDiag

--import Game.StructInstWithHoles

World "Robotswana"
Level 8

Title "Die Summe der Summe der Summe"

Introduction
"
再び手がかりを見つけましたが, 急いでいるうちに道を見失いました. 
あなたは今, とても喉が渇いています. 
Roboが周辺を探している間, あなたは疲れ果てて座り込み, 
暖かい日差しの中で少しぼんやりと羊皮紙の切れ端を眺めています. 
"

Conclusion "**あなた**: やっとだ. 

Roboがあなたに水の入ったボトルを手渡す. 

**あなた**: いったいどこから手に入れたの? 

**Robo**: トリック17だよ. 

**あなた**: それで, 道は見つかった? 

**Robo**: ああ, ついてきて！あそこに何か見えたんだ. "

open Nat Matrix StdBasisMatrix Finset

/---/
TheoremDoc Matrix.eq_sum_apply_diag_ebasis as "eq_sum_apply_diag_ebasis" in "Matrix"

Statement Matrix.eq_sum_apply_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))
    (A : Mat[n,n][ℝ]) :
    f A = ∑ i : Fin n, (A i i) * f (E i i) := by
  Hint "**あなた**: これはいったい…? 

  あなたは少し落書きをする. 

  $$
  \\begin\{aligned}
    f(A)
    &= f\\left( \\sum_\{i,j} A_\{i,j} \\cdot E_\{i,j} \\right) \\\\
    &= \\sum_\{i,j} A_\{i,j} \\cdot f(E_\{i,j})   \\\\
    &= \\sum_\{i} A_\{i,i} \\cdot f(E_\{i,i})
  \\end\{aligned}
  $$

  **あなた**: そうか, こうすればいいんだ. `A`を基底行列の和として書き, 
  線形性を利用し, 最後に`f`が`i ≠ j`の`E i j`で消えることを使う. 

  おそらく最初に`f A`の`A`を基底行列の和として書くべきだ. 

  **Robo** (*遠くから*): `nth_rw 1 [ ... ]`！`rw`のように使えるよ. "
  Hint (hidden := true) "**あなた** (*叫びながら*): どういうこと? 

  **Robo** (*同じく叫びながら*): `matrix_eq_sum_ebasis A`を使いたいんだろうけど, `rw`じゃなくて`nth_rw 1`で. "
  Branch
      rw [matrix_eq_sum_ebasis A]
      Hint "**あなた**: `rw`は良くないな. 複雑すぎる. `nth_rw`で試してみよう. "
  nth_rw 1 [matrix_eq_sum_ebasis A] -- Lvl 3
  Hint "**あなた** (*心の中で*): 線形性を使う…そして水のことを考えないように…バビロンには十分な水があった…何をしてたんだっけ? "
  Hint "**Robo** (*どこからか*): `map_sum`みたいだね. バビロンでは見なかったと思うけど, 想像してるんだろう. でも`simp`はこの補題を知ってるはず. "
  Branch
    simp
  rw [map_sum] -- simp knows this
  Hint "**あなた**: ああ, 迷ったら簡略化だ. "
  simp
  Hint "**Robo**: 今どこまで進んだ? 

  **あなた**: `i≠j`の`E i j`で`f`が消えることをどうにかして入れないと. 

  **Robo**: 次の中間ステップをやってみて:

  `trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0`"
  trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0
  · Hint "**Robo**: 和は和と等しい…`apply congr_arg`, `ext`で攻めるんだ. "
    apply congr_arg
    ext i
    Hint (hidden := true) "**あなた**: もう一度やる? "
    apply congr_arg
    ext j
    Hint "**あなた**: そして`{i} = {j}`で場合分け…"
    Hint (hidden := true) "**Robo**: `by_cases`だよ, そう！"
    by_cases h₂ : i = j
    · Hint "**Robo**: ここは`if_pos {h₂}`が役立つ. "
      rw [if_pos h₂]
    · Hint "**Robo**: …そしてここは`if_neg {h₂}`. 

      **あなた**: 知ってるよ. "
      rw [if_neg h₂]
      Hint "**あなた**: `f (E i j)`はゼロだよね, 前に見た！"
      Hint (hidden := true) "**Robo**: それは`zero_on_offDiag_ebasis`だった. "
      rw [zero_on_offDiag_ebasis]
      · simp
      · assumption
      · assumption
  · Hint  "**あなた**: もう終わりかと思った. 

    **Robo**: ほぼ, `trans`コマンドの後半が残ってる. これは簡単だ. "
    simp

-- TODO: Where to introduce it? It is for additive `f : A →+ B`, so Babylon might not be ideal
/--
Lineare Abbildungen (oder genereller "additive" Abbildungen) kann man mit einer
Summe vertauschen.
-/
TheoremDoc map_sum as "map_sum" in "∑ Π"

TheoremTab "Matrix"
NewTheorem map_sum
