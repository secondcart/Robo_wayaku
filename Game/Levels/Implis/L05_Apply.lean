import Game.Metadata

World "Implis"
Level 5

Title "Implikation"

Introduction
"
次のページは少し複雑に見えます。混乱しないように、ロボがすぐにさまざまな含意を図式にまとめます。
  $$
  \\begin{CD}
       A  @>{f}>> B @<{g}<< C    \\\\
    @V{h}VV    @V{i}VV   @V{j}VV \\\\
       D  @<{k}<< E @>{l}>> F    \\\\
    @A{m}AA    @A{n}AA   @V{p}VV \\\\
       G  @<{q}<< H @>{r}>> I
  \\end{CD}
  $$
"
Statement
    (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) (k : E → D) (l : E → F)
    (m : G → D) (n : H → E) (p : F → I) (q : H → G) (r : H → I) : A → I := by
  Hint "
    **あなた**: つまり、$A \\Rightarrow I$ の含意の経路を見つけなければならない。

    **ロボ**: どう始めるか考えてみよう…また `intro` かな？"

  intro hyp
  Hint (hidden := true) "**ロボ**: やっぱり `apply` でしょ。"
  Branch
    apply r
    Hint "**ロボ**: これは行き止まりみたいだ…"
  Branch
    apply p
    Branch
      apply j
      Hint "**ロボ**: これは良くないね。"
    apply l
    Branch
      apply n
      Hint "**ロボ**: うーん、何か間違ってる…"
    apply i
    Branch
      apply g
      Hint "**ロボ**: 待って！道を間違えたよ。"
    apply f
    assumption
  Branch
    apply h at hyp
    Hint "**ロボ**: 本当にそれでいい？"
  apply f at hyp
  apply i at hyp
  Branch
    apply k at hyp
    Hint "**ロボ**: えっと…"
  apply l at hyp
  apply p at hyp
  assumption

Conclusion
"
作戦責任者は再び丁寧にお礼を言いました。彼は再びいくつかのボタンを押し、
大きなガタンという音と共に、いくつかのコンベアが同時に再起動します。
"

DisabledTactic tauto
