import Game.Metadata


World "Babylon"
Level 6

Title "" -- "Arithmetische Summe"

Introduction
"
**Babylon人**: さあ, 私たちの最も美しい塔の一つをお見せしましょう! 

道は険しい山道を登っていきます. 山頂で待つ塔は, 実に壮大なものです. 

**Robo**: これは有名な『Babylonのガウス塔』に違いありません! 
それについて一度読んだことがあります. 

**Babylon人**: その通り. ガウスはBabylon人でした! 
"

open Finset
open Robo.NN.Finset -- temporary solution to make correct version of `insert_Icc_eq_Icc_add_one_right` available

/---/
TheoremDoc arithmetic_sum as "arithmetic_sum" in "∑ Π"

-- This would also easily work as a sum in ℚ,
-- and BOSS level would even be easier to prove in ℚ,
-- but cannot get initial conversion to ℚ to work!

Statement arithmetic_sum (n : ℕ) :
     (∑ i ∈ Icc 0 n , i : ℚ) = 1/2  * n * (n + 1) := by
  Hint "**あなた**: この和は以前見たことがあります. 
    $$
    \\sum_\{i = 0}^n i = \\tfrac\{1}\{2} \\cdot n \\cdot (n + 1)
    $$

  ガウス少年がとても簡単な証明をしたという話ではありませんでしたか? 

  **Robo**: 歴史の話はわかりません. 私は単に`n`についての帰納法を使うでしょう. 
  それはLeanでは`induction n with d hd`です! 

  **あなた**: なぜ`with …`が必要なのですか? 

  **Robo**: もちろんこの追加はオプションです. 
  これで帰納変数(`d`)と帰納仮説(`hd`)の名前を指定できます. "
  induction n with d hd
  Hint "**あなた**: まず帰納法の基底ケース…

  **Robo**: これはしばしば`simp`で簡略化できます! "
  simp
  Hint "**Robo**: 今, 和を取る区間$[0, {d}+1]$を$[0,{d}]$と${d}+1$に分割したいですね. 
    そのためには, 以前見た`insert_Icc_eq_Icc_add_one_right`という補題が使えます. 
  "
  rw [← insert_Icc_eq_Icc_add_one_right]
  Hint "**Robo**: そうです! そして今, `sum_insert`が和をあなたが望むように正確に分割します：
  $[0,{d}]$の和と, ${d}+1$の追加項です. 
  試してみてください：`rw [sum_insert]`
  "
  rw [sum_insert]
  Hint (hidden := true)
  "**あなた**: そして今, 帰納仮説をどのように適用すればよいですか? 

  **Robo**: 他の仮定と同じように`rw`で使えます. "
  rw [hd]
  Hint "
    **あなた**: 残りは単なる計算のはずです. 

    **Robo**: その通りです. `simp`と`ring`の組み合わせで解決できるはずです. 
  "
  simp
  ring
  simp
  linarith

NewTactic induction

/---/
TheoremDoc Finset.sum_insert as "sum_insert" in "∑ Π"
NewTheorem Finset.sum_insert

-- Nat.zero_eq
-- Nat.succ_eq_add_one
-- Fin.sum_univ_castSucc

TheoremTab "∑ Π"

Conclusion ""
