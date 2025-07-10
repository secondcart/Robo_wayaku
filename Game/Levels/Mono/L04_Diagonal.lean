import Game.Levels.Mono.L03_NotInjective

World "Mono"
Level 4

Title "" -- ""

Introduction ""

open Function Nat

-- How we write the definition of `diag` – whether as `(fun a _ ↦ a)` or `fun a ↦ (fun i ↦ a)`  or `…`
-- does not affect the way it is displayed in the game!

Statement {A : Type} (n : ℕ) :
    let diag : A → Fin (n + 1) → A := fun a i ↦ a
    Injective (diag) := by
  Hint "**あなた**: diagの定義には再び2つの矢印が連なっています。まず頭の中で整理する必要があります。

  **Robo**: 最初に括弧を付けましょう: `A → (Fin (n + 1) → A)`。つまりdiagはAから集合Fin (n + 1) → Aへの写像です。
  `Fin (n+1)`は集合$\\\{0,1,…,n\\}$であり, `Fin (n + 1) → A`は$\\\{0,1,…,n\\}$から$A$への写像の集合です。

  **あなた**: ええと…そのような写像は実際にはAの要素の(n+1)タプルに他なりませんね？

  **Robo**: そう考えることもできます。

  **あなた**: わかりました。与えられているのはAから$A^\{n+1}$への写像diagです。そしてそれは…ああ, なぜこれがdiagと呼ばれるのかわかります。"
  Hint (hidden := true) "**あなた**: それとも違うのでしょうか？もう一度分解してもらえますか？

  **Robo**: 写像diagは要素aを, すべてのインデックス$i \\in \\\{0,1,…,n\\}$を$a$に写す写像に送ります。
  あなたの解釈では, これはa ↦ (a,…,a)という写像です。"
  Hint (hidden := true) "**Robo**: どうしてもわからない時は, まず `unfold Injective` から始めるのが良いでしょう。"
  --unfold Injective
  Branch
    simp [diag]
    intro a b h
    Hint (hidden := true) "**Robo**: `{h}` の写像を `Fin (n + 1)` の要素で評価してみてはどうでしょうか？おそらく `congr_fun` が何らかの形で役立つかもしれません。"
    apply congr_fun at h
  --Branch
  --  apply HasLeftInverse.injective  -- not yet known!
  --  let p : (Fin (n + 1) → A) → A := fun v ↦ v (Fin.last n)
  --  use p
  --  tauto
  intro a₁ a₂ h
  Hint (hidden := true) "**Robo**: あなたの「タプル」 `diag {a₁}` と `diag {a₂}` は実際には `Fin (n + 1) → A` の2つの写像であることを思い出してください。
これらを `Fin (n + 1)` の要素で評価してみてはどうでしょうか？おそらく `congr_fun` が何らかの形で役立つかもしれません。"
  apply congr_fun h 0
