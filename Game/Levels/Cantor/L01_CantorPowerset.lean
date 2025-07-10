import Game.Metadata

World "Cantor"
Level 1

Title "Cantor's Diagonalargument"

Introduction
"
**カントール**: … 我々は集合`A`からその冪集合への写像`f`を考え, 
そして`A`の要素で`f`による像に含まれないもの全ての集合を…

おや！観客がいる. いや, *二人*の観客だ！聞け, 見よ, 驚くがいい. 

彼はシルクハットから紙片を取り出し, ツバメのように折りたたみ, 
あなた方へと飛ばしてくる. 

**カントール**: 二人の観客がいるのなら, 少し参加してもらおうじゃないか？
"

Conclusion ""

open Set Function

Statement {A : Type} (f : A → Set A) : ¬ ∃ (a : A), f a = { x | x ∉ f x } := by
  --Hint "**Robo**: Denk daran, dass `mem_setOf` aus `Set` irgendwann hilfreich sein wird."
  Hint "**あなた**: つまり`Set A`は`A`の冪集合なの？

  **Robo**: まあそういうことだね. `A`の全ての部分集合の集合, より正確には型だ. 

  **あなた**: そして私が示すべきは…なるほど. おそらく背理法かな？

  **Robo**: おそらくね. 
  "
  Branch
    push_neg
    intro _a
    by_contra _ha
  by_contra h
  Hint "**カントール**: よしよし！さあ`{h}`をきれいに分解しよう…"
  Hint (hidden := true)"**Robo: …いつものように`obtain`でね"
  obtain ⟨a, ha⟩ := h
  Hint (strict := true) "**あなた**: 今度は`{a} ∈ {f} {a}`について場合分けする？"
  Hint (hidden := true) (strict := true) "**Robo**: `by_cases h₁ : {a} ∈ {f} {a}`だね"
  by_cases h₁ : a ∈ f a
  Hint "カントールは手を擦り合わせる. 

    **カントール**: いい調子だ！
    "
  · Branch
      rw [ha] at h₁
      Hint "
        **カントール**: 良い考えだ！ほぼ正解！
        だが元の仮定`{h₁} : {a} ∈ {f} {a}`がもう一度必要になるだろう. 

        **Robo**: 了解, 戻って`have`で続けよう. 
        または`suffices : {a} ∉ {f} {a}`で！
        "
    suffices : a ∉ f a
    · contradiction
    rw [ha] at h₁
    simp at h₁ --or: rw [mem_setOf] at h₁
    assumption
  · apply h₁
    rw [ha]
    simp --or: rw [mem_setOf]
    assumption

TheoremTab "Set"

Conclusion "カントールは手を叩いて喜ぶ. 
魔法のように紙片は彼のもとへ飛んで帰っていった. "
