import Game.Metadata


World "Vieta"
Level 2

Title "Anonyme Funktionen"

Introduction
"
再び矢がかすめて飛んでいきます. しかしVietaは冷静に次の紙を渡してきます. 
"

Statement : let f : ℤ → ℤ := fun x ↦ x ^ 2; f 2 = 4 := by
  Hint "
    **Robo**: ああ, これはもっと興味深いですね. ここで
    `fun (x : ℤ) ↦ x ^ 2` は「匿名関数」, つまり写像 $x↦x^2$ です. 

   **あなた**: そして, 何が匿名なのですか？

   **Robo**: そうですね, 最初は名前がないということです. 
    `f : ℤ → ℤ := …` によって初めて名前が与えられます. 

  **あなた**: なるほど. つまり全体として次のような写像ですね？

    $$
    \\begin\{aligned}
      f\\colon \\mathbb\{ℤ} &\\to \\mathbb\{ℤ} \\\\
      x &\\mapsto x ^ 2
    \\end\{aligned}
    $$

  私は $2^2=4$ を示せばいいのですか？

  **Robo**: はい. 

  **あなた**: そしてここでどうすればいいですか？

  **Robo**: Leanはほとんどの写像の定義を見通せるので, ここでは `rfl` で十分です. 
  別の方法として `simp [{f}]` で明示的に定義を代入することもできます. "
  Branch
    simp [f]
  rfl


NewDefinition Symbol.function
TheoremTab "Function"

Conclusion ""
