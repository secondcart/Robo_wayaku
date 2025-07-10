import Game.Metadata


World "Vieta"
Level 4

Title "" -- "let"

Introduction
"
**Vieta**: さあ, ここを少し移動しなければなりません. 

彼は慎重にあなた方を数メートル先へと押しやる. その瞬間, あなた方が今立っていた場所に3本の矢が降り注ぎ, 地面に突き刺さる. 

**Vieta**: 落ち着いて, 私はこの辺りに詳しいんです. ほら, あなた方のためにまだ持っていますよ. 
"


open Function

Statement (x : ℤ) :
    let f : ℤ → ℤ := fun x ↦ x + 5
    ∃ (g : ℤ → ℤ), (g ∘ f) x = x + 2 := by
  Hint "
    **あなた**: `g ∘ {f}` は写像の合成ですか? 

    **Robo**: 正解です！それは`\\comp`で書きます. 

    **あなた** ではここでまた
    `let g : ℤ → ℤ := fun x ↦ _`と定義できますか? 

    **Robo**: はい, または直接`use fun (x : ℤ) ↦ _`も使えますよ? "
  Branch
    let g : ℤ → ℤ := fun x ↦ x - 3
    Hint "**Robo**: これで`use {g}`を使ってください. "
    use g
    Hint "
    **Robo**: `({g} ∘ {f}) x`は定義により`{g} ({f} x)`です. `simp`もこの
    補題を知っていますが, ここでは直接`rw [comp_apply]`を使ってみてください. "
    Hint "
    **Robo**: `ring`は`{f}`や`{g}`のようなローカル定義を
    見通せるので, 直接使えます. "
  use fun (x : ℤ) ↦ x - 3
  Hint "
  **Robo**: `(g ∘ {f}) x`は定義により`g ({f} x)`です. `simp`もこの
  補題を知っていますが, ここでは直接`rw [comp_apply]`を使ってみてください. "
  rw [comp_apply]
  Hint "
  **Robo**: `ring`は`{f}`のようなローカル定義を
  見通せるので, 直接使えます. "
  ring

/--
Sagt dass `(f ∘ g) x` das gleiche ist wie `f (g x)`.
-/
TheoremDoc Function.comp_apply as "comp_apply" in "Function"

NewTheorem Function.comp_apply
DisabledTactic simp -- simp_rw
TheoremTab "Function"

Conclusion ""
