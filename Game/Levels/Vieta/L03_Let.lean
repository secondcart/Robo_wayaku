import Game.Metadata


World "Vieta"
Level 3

Title "Anonyme Funktionen"

Introduction
"
また矢印だ. そしてまた課題だ. 
"

Statement : ∃ f : ℤ → ℤ, ∀ x, f x < x := by
  Hint (hidden := true) "
    **Robo**: いつものように, `∃`には`use …`でアプローチする. または, `let f : ℤ → ℤ := fun …`で, 先ほど見たように使いたい写像を定義しても良い. 
    矢印`↦`は`\\maps`または`\\mapsto`で書く. 代わりに`=>`を使っても良い. "
  let f : ℤ → ℤ := fun x ↦ x -1
  Hint (strict := true) "**Robo**: `{f}`を正しく定義できたら, `use`で使える. 結果の不等式は簡単になるはずだ"
  use f
  intro x
  Hint (hidden := true) "**あなた**: これはどう簡略化されるんだろう? "
  simp [f]
  -- linarith

TheoremTab "Function"

Conclusion""

--NewTactic «let»
