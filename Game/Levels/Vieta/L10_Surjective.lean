import Game.Metadata


World "Vieta"
Level 10

-- "A function which semiconjugates an endofunction to the successor function is surjective"
Title "" -- "Boss"
Introduction
"
戦闘音が今や危険なほど近くに聞こえる. 
はっきりと大砲の音が聞こえる. 
そしてまた矢があなたの横をかすめて飛んでいく. 

**あなた**: えーと, 私たちは多分…

**Vieta**: 心配しないで, まだ1つの課題をする時間はあるよ. 
"

open Function Nat

Statement {A : Type} {f : A → ℕ} (h : ∃ a : A, f a = 0) {g : A → A}
    (hs : f ∘ g = succ ∘ f) : ∀ n, ∃ a, f a = n := by
  Hint "
    **あなた**: ここでの`succ`って何? 

    **Robo**:  `succ : ℕ → ℕ`は自然数をその*successor*(後継者), つまり次の数に写す関数です. 
    言い換えれば: `n ↦ n + 1`. 

    **あなた**: ああそうか. そしてこの写像`f`は, 正しく読めば基本的に全射であることを示す必要があるんだね. 

    **Robo**: そのようだ！
  "
  Hint (hidden := true)"
  **Robo**: 見て, 写像は`ℕ`に向かっているよ！

  あなたは眉を上げる. 

  **Robo**: 帰納法と関係があるかもしれない. ただの提案だけど. 
  "
  intro n
  induction n with n hn
  · assumption
  · obtain ⟨b, hb⟩ := hn
    use g b
    Branch
      rw [← hb]
      apply congr_fun hs
    Hint (hidden := true) "**Robo**: もしかして`congr_fun`を使って仮定`{hs}`を
    `∀ x, ({f} ∘ {g}) x = (succ ∘ {f})`に書き換えたい? "
    apply congr_fun at hs
    specialize hs b
    simp at hs
    rw [hs]
    rw [hb]

Conclusion  "
**Vieta**: ブラボー！ でも今はここから急いで離れることだ. 
こっちだ. 宇宙船まで連れて行ってあげる. 
"
NewDefinition Nat.succ
