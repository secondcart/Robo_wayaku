import Game.Metadata


World "Vieta"
Level 6

Title "Stückweise Definition"

Introduction
"
**Vieta**:  もう少し歩きましょう. こちらへ! 

彼は急ぎ足で去り, あなたはできるだけ速く追いかけます. 
彼が最終的に立ち止まった場所に到着した時, あなたは完全に息切れしています. 
Vietaは笑います. 

**Vieta**:  これは予防措置です! 訪問者の面倒を見なければなりませんから. 
こんなに訪問者が来ることは滅多にないんです! 

彼は次の紙をあなたに手渡します. 
"

open Set Function

Statement :
    let f : ℚ → ℚ := fun x ↦ 5 * x
    let g : ℚ → ℚ := fun x ↦ if 0 ≤ x then 2*x else 0
    f ∘ g = g ∘ f := by
  Hint "
    **Robo**: 今私たちは2つの写像を持っています, そのうち1つは区分的な定義です. 

    **あなた**: つまり, これらが交換可能であることを示せばいいのですか? 

    **Robo**: その通りです. `funext x`を使って任意の要素を選び, それを示すのがベストです. "
  funext x
  Hint "
    **あなた**: ああ, まず`(g ∘ f) {x}`を`g (f {x})`と書き換えられるのですか? 

    **Robo**: `simp`でできます. "
  simp -- or simp [f, g]
  -- TODO: add `(defeq := _)` so that this triggers for `simp [f, g]` too
  Hint (strict := true) "
    **Robo**: これで場合分けができます, `by_cases h : 0 ≤ {x}`. 

    **あなた**: これで`0 ≤ {x}`と`0 > {x}`の場合が得られますか? 

    **Robo**: はい! 正確には`0 ≤ {x}`と`¬(0 ≤ {x})`です. これは完全に同じではなく, 
    `not_le`という補題を使って`¬(0 ≤ {x})`と`0 > {x}`を切り替えられます. "
  by_cases h : 0 ≤ x
  · Hint "**あなた**: 定義を使う必要がありそうですね. 

    **Robo**: では`simp [f, g]`を使ってください! "
    simp [f, g]
    Hint "
      **Robo**: これで`rw [if_pos {h}]`を使ってif-then-elseを簡約できます. "
    rw [if_pos h, if_pos h]
    ring
  · Hint (hidden := true) "**Robo**: もう一度`simp [f, g]`を. "
    simp [f, g]
    Hint "**あなた**: ああ, `if_pos`の否定はきっと..."
    Hint (hidden := true) "**Robo**: `if_neg`です, その通り! "
    rw [if_neg h, if_neg h]

Conclusion ""

/---/
TheoremDoc if_neg as "if_neg" in "Logic"
/---/
TheoremDoc if_pos as "if_pos" in "Logic"

NewTheorem if_pos if_neg

TheoremTab "Logic"
