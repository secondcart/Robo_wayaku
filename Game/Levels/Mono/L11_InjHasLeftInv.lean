import Game.Levels.Mono.L10_Auxiliary

World "Mono"
Level 11

Title "" -- "Injections have a left inverse, and vice versa"

Introduction
"
"

open Set Classical

/---/
TheoremDoc Function.injective_iff_hasLeftInverse as "injective_iff_hasLeftInverse" in "Function"

namespace Function

Statement injective_iff_hasLeftInverse {A B : Type} [hA : Nonempty A]  (f : A → B) :
  Injective f ↔ HasLeftInverse f := by
  Hint "
    **あなた**: なるほど。エポソ派は, 写像が全射であることと右逆元を持つことが同値であることを証明したかったのですね。
    そしてここのモノソ派は, 写像が単射であることと左逆元を持つことが同値であることを証明したかったのですね。

    **Robo**: はい, ただし彼らはこの追加条件`Nonempty A`が必要な点が違います。
  "
  Hint (hidden := true) "
      **あなた**: 具体的に左逆元をどう構築すればいいか分かりません。

      **Robo**: 先ほど証明した命題を思い出してください: ` ∀ b : B, ∃ a : A, …`
      これがあれば, おそらく`choose`を使って求められる左逆元を選択できます。
      ただ残念ながらこの命題には名前がついていません。
      おそらく`have`で再度定式化し, 証明し直す必要があるでしょう。
    "
  constructor
  · intro hf
    Branch
      -- alternative construction of inverse `g` as a branched function
      -- strongly uses `Classical`,
      -- unsure how to complete the proof this way
      obtain ⟨a₀⟩ := hA
      let g' (b : B) (h : (∃ a : A, f a = b)) : A := by
        choose a ha using h
        exact a
      let g : B → A := fun b ↦ if h : (∃ a : A, f a = b) then g' b h else a₀
      use g
      intro a
      apply hf
      simp [g,g']
    have : ∀ b : B, ∃ a : A, f a = b ∨ ¬ ∃ a' : A , f a' = b := by
      /- exactly L10_Auxiliary, now without hints -/
      obtain ⟨a₀⟩ := hA
      intro b
      by_cases hb : ∃ a' : A, f a' = b
      · obtain ⟨a,ha⟩ := hb
        use a
        left
        assumption
      use a₀
      right
      assumption
    choose g hg using this
    use g
    intro a
    apply hf
    obtain hpos | hneg := hg (f a)
    · assumption
    · push_neg at hneg
      have : f a ≠ f a := hneg a
      contradiction
  · /- Injective f → HasLeftInverse f
       exactly L09_injOfHasLeftInv, now without hints-/
    Hint (hidden := true) "
      **Robo**: これは前に証明した内容ですね…しかし保存し忘れていました。
      証明を覚えていますか？
    "
    intro hL
    intro a a' ha
    obtain ⟨g, hg⟩ := hL
    apply congr_arg g at ha
    unfold LeftInverse at hg
    rw [hg a, hg a'] at ha
    assumption

Conclusion "
再び大きな拍手を受けて, あなた方は見送られます。
帰路のための輸送カプセルはまたしてもありません。
しかし, それほど遠くもないでしょう。
"
