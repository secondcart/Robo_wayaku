import Game.Metadata


World "Iso"
Level 2

Title "Inverse"
Introduction
"
**イソソフ**:  …そして本題に入りましょう. 
"

namespace Function


--TODO: `unfolding` at random places breaks all the hints...

/---/
TheoremDoc Function.bijective_iff_has_inverse as "bijective_iff_has_inverse" in "Function"

Statement bijective_iff_has_inverse {A B : Type} (f : A → B) :
    Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f := by
  Hint "**あなた**: 写像が全単射であることと, それに対する逆写像が存在することは同値です. 
  これは基本的に, EpoとMonoで既に示したことと同じです. 
  これらの主張を保存していましたか? 

  **Robo**: はい, しかしここでそれらを展開すると眉を上げられるでしょう. 
  代わりに, しっかり考えて, それがどうだったか思い出しましょう. 
  "
  constructor
  · intro h
    Hint (hidden := true)"
      **Robo**: まず`Bijective`を`obtain ⟨hinj, hsurj⟩  := {h}`で
      `Injective`と`Surjective`に分解してみてください！"
    obtain ⟨finj, fsurj⟩  := h
    Hint (hidden := true)"
      **Robo**: 全射性から, 各`y : B`には原像`x : A`があることが分かります. 
      `choose`を使って逆写像を構築できませんか? "
    choose g hg using fsurj
    Hint "
      まず`{g}`が`{f}`の右逆元であることを示すのが良いでしょう, 
      例えば`have hR : RightInverse {g} {f}`のように"
    have hR : RightInverse g f := by
      assumption
    use g
    constructor
    · --Branch
      --  apply rightInverse_of_injective_of_leftInverse finj  -- das ist Mono, L08, aber wir haben das Lemma nicht gespeichert.
      --  assumption
      Hint (hidden := true)"**Robo**: `simp [LeftInverse]`で証明目標を簡略化できます. "
      simp [LeftInverse]
      Hint (hidden := true) "**Robo**: `intro`から始めてみては? "
      intro x
      have : f (g (f x)) = f x  := by rw [hR]
      Branch
        apply finj at this
        assumption
      apply finj
      assumption
    · assumption
  · intro h
    --obtain ⟨g, hL, hR⟩ := h
    Hint (hidden := true) "**Robo**: `{h}`をできるだけ分解してください！"
    obtain ⟨g, h⟩ := h
    Hint (hidden := true) "**Robo**: ANDもさらに分解！"
    obtain ⟨hL, hR⟩  := h
    constructor
    Hint (hidden := true) "
      **Robo**: 単射性が難しい部分です. まず`intro`から始めてみてください. "
    · intro a b eq
      rw [← hL a, ← hL b]
      --Branch
      --  congr -- not used in this game
      Hint (hidden := true) "
        **あなた**: 引数`f a = f b`が等しいなら`g (f a) = g (f b)`も等しい—
        どう言えばいいんだっけ? 

      **Robo**: `f a = f b`があるなら, 単に`rw`を使えますよ. "
      rw [eq]
    · intro b
      use g b
      Hint (hidden := true) "
        **Robo**: ここでは`RightInverse`の仮定を`rw`で使えます. "
      rw [hR]


TheoremTab "Logic"
DisabledTheorem Function.injective_iff_hasLeftInverse Function.surjective_iff_hasRightInverse

Conclusion
"
イソソフたちはとても満足そうでした. 

**Robo**: 私たちはもう一度...カプセル化できますか? 

**イソソフ**: もちろん！ しかし順序よく進めましょう. 
私たちが双方向でカプセルを使い始めてから, また事故が増えています. 

Roboはさらに3往復します. その後, あなたたちはさらに進みます. 
"
