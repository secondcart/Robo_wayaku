import Game.Metadata

World "Babylon"
Level 5

Title ""

Introduction
""

open Finset Nat

Statement  (I : Finset ℕ) : ∑ i ∈ I, ((-1 : ℤ)^i + 1) = 2*card { i ∈ I | Even i} := by
  Hint "
    **あなた**: ここで示すべきことは
    $$
    \\sum_\{i \\in I} \\left( (-1)^i + 1 \\right)
    $$
    がI内の偶数の数の2倍に等しいということですよね? 

    **Robo**: その通りです. 

    **あなた**: そしてそれは...和の中の式が奇数iでは0になり, 
    偶数iでは2になるからです. うーん...

    **Robo**: `trans`を使って中間ステップを作りましょう. まず和を偶数インデックスの集合に制限します：
    ```
    ∑ i ∈ \{ i ∈ I | Even i}, ((-1)^i + 1)
    ```
    その後, おそらく
    ```
    ∑ i ∈ \{ i ∈ I | Even i}, 2
    ```
    を中間ステップとして使いたいのでしょう. 
  "
  trans ∑ i ∈ { i ∈ I | Even i}, ((-1)^i + 1)
  · Branch
      rw [sum_subset]
      Hint "
        **Robo**: これは何か間違っているようです...
        `sum_subset`を逆に適用した方が良いかもしれません. 
        またはこのステップの前に`symm`で等式を反転させてください. 
        "
    symm
    apply sum_subset
    · simp
    · simp
      intro i h hI
      apply hI at h
      rw [Odd.neg_pow]
      ring
      rw [← odd_iff_not_even] at h
      assumption
  · trans ∑ i ∈ { i ∈ I | Even i}, 2
    have : ∀ i ∈ { i ∈ I | Even i}, (-1 : ℤ)^i + 1 = 2 := by
      Hint (hidden := true ) "
        **Robo**: これについては以前`Even.neg_pow`と`Odd.neg_pow`を見たことがありますね. 
      "
      intro i hi
      simp at hi
      obtain ⟨hI, heven⟩ := hi
      rw [Even.neg_pow]
      ring
      assumption
    Hint (hidden :=true) "
      **Robo**: 良さそうです. これで`sum_congr`を使える段階です. 
    "
    apply sum_congr   -- introduced above
    · simp
    · assumption
    Hint (hidden := true) "
      **Robo**: もう一度`simp`を試してみてください. 
    "
    simp
    ring

TheoremTab "∑ Π"

Conclusion "
  **バビロニア人**: よくできました. 
"
