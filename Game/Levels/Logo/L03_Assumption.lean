import Game.Metadata

World "Logo"
Level 3

Title "Annahmen"

Introduction
"
最初の家臣がまだ「`rfl`, `rfl`, `rfl`」とつぶやいている間に, 次の家臣が前に出てきます. 
それは恥ずかしがり屋で, ただ書き留めるだけです. 
"

set_option linter.unusedVariables false in

Statement (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) (h₃ : n ≠ 5) : 1 < n := by
  Hint "
  **Robo**: `{n} : ℕ` は, `{n}` が自然数であることを意味します. 

    **あなた**: それならなぜ `{n} ∈ ℕ` と書かないの? 

    **Robo**: ここではみんな変なタイプだから…後でゆっくり説明するよ. 今はまず問題を解読したいんだ. 

    **Robo**: つまり, `{h₁}`, `{h₂}`, `{h₃}` は, それぞれ `n < 10`, `1 < n`, `n ≠ 5` という仮定の名前だ. 証明すべきは `1 < n`. 

    **あなた**: でもそれは仮定の一つじゃない? 

    **Robo**: そうだね. 

    **あなた**: ???

    **Robo**: それを明確に伝えないといけないんだ. `assumption` を使ってみて. "
  assumption

Conclusion
"
**家臣**: はい, 正解！この問題でどれだけ頭を悩ませたか, あなたが知っていたら！
"

NewTactic assumption
DisabledTactic tauto
