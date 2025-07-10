import Game.Levels.Robotswana.L09_EvalOnEBasis

World "Robotswana"
Level 10

Title "" -- "Trace"

Introduction
"
ゆっくりと忍び寄る. 

**あなた**（小声で）: 君の言う通りだったみたい. これらのメモは一種の特徴リストだ！
そしてこれは明らかにここの生き物を説明している！

**Robo**: どういう意味？

**あなた**: 見てよ, その大きさ, 交換子への好み, その他の全ての特徴, 
これで明確に識別できる！

**Robo**: もっと詳しく説明してくれ. 

**あなた**: やってみるよ. Leanには跡(trace)の名前がある？

**Robo**: ああもちろん, `trace`って呼ばれてるよ. 一部の形式主義者はTracyって愛称で呼んでる. 

あなたは羊皮紙の切れ端を一枚取り, 裏側に書き始める. 
"

Conclusion "
**Robo**: その通りだ. 君の言う通りだった. 

あなたたちはこの惑星で明らかに唯一無二のこの生き物を観察し, 満足げに見つめる. 

近づくと, Tracyが気づいたようだ. しかし特に邪魔されている様子はない. 
"

open Nat Matrix StdBasisMatrix Finset

/---/
TheoremDoc Matrix.trace_eq as "trace_eq" in "Matrix"

Statement Matrix.trace_eq {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    trace = f := by
  Hint "**あなた**: ここに全ての性質がまとめられているよ. 

    **Robo**: そして君は, Tracyだけがこれらの性質を持つと言うのかい？

    **あなた**: そうだよ. そう信じてる. どんな`f`でもこれらの性質を持てば, 全ての行列でTracyと同じように振る舞う. だからそれはTracyなんだ！"
  Hint (hidden := true) "
    **Robo**: `ext`!"
  ext A
  Hint "**あなた**: そして今, `f {A}`を基底要素の和として書こう. "
  rw [eq_sum_apply_diag_ebasis] -- Lvl 7
  Hint "
    **あなた**: `induction n`?

    **Robo**: 試してみて！
    "
  induction n with d hd
  · Hint (hidden := true) "**Robo**: 頭の中で`simp`を試したよ. 君も試してみて. "
    simp
  · clear hd
    Hint "**あなた**: さっき`f (E i i) = 1`ってわかったよね！

      **Robo**: 調べるのは得意だよ！`one_on_diag_ebasis`だった. "
    Hint (hidden := true) "
      **Robo**: `one_on_diag_ebasis`にはいくつかの前提が必要だ. 
      `{d} + 1 > 0`という前提をまず`have`で確認しておくといいよ. 
      "
    --simp at h₂
    have : d + 1 > 0 := by
      omega
    Hint (hidden := true) "
      **Robo**: `one_on_diag_ebasis`の等式も`simp`で使えるよ！
    "
    simp [one_on_diag_ebasis this h₁ h₂] -- Lvl 8
    Hint (hidden := true) "**Robo**: 両辺は定義的に等しいよ！"
    rfl
  Hint "**あなた**: この証明目標はどこから来たんだっけ？

  **Robo**: 最初の`rw [eq_sum_apply_diag_ebasis]`でこの引数を省略したんだよ. 今ならまだ追いつける. "
  assumption

/--

Nicht genau definiert als, aber per Definition äquivalent zu:
`trace A = ∑ i, A i i`.

mathlib benutzt den Term `diag A i` auf den wir hier nicht genauer eingehen.

-/
DefinitionDoc Matrix.trace as "trace"

NewDefinition Matrix.trace
TheoremTab "Matrix"
