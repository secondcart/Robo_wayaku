import Game.Metadata

World "Implis"
Level 8

Title "Genau dann, wenn"

Introduction
"
**オペレーションマネージャー**: ここで, これについて何か言えることはありますか？
"

Statement (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  Hint "
    **あなた**: $B \\iff A \\iff D \\iff C$, これらはすべて同値ですね…

    **Robo**: はい, しかし彼が同値関係を書き換えるのを手伝う必要があります. `rw [h₁]`を使えば, 
    `C`を`D`に置き換えることができます. "
  rw [h₁]
  Hint "
     **あなた**: 逆方向に書き換えたい場合はどうすればいいですか？

    **Robo**: その場合は名前の前に`←`（`\\l`, つまり小文字の「L」）を書きます. つまり`rw [← hₓ]`です. "
  Branch
    rw [← h₃]
    Hint "
      **あなた**: ええと, それは間違いでした. 

      **Robo**: はい, 逆方向の方が良かったですね. しかし, 今のまま進めて, 
      `A ↔ A`のような式を得たら, `rfl`で証明できます. 

      **Robo**: そういえば, `rw`は自動的に`rfl`も試みます. 
      つまり, `rfl`を明示的に書く必要はありません. "
    rw [h₂]
  rw [←h₂]
  assumption

Conclusion
"
**オペレーションマネージャー**: この調子で進めれば, この山を全部片付けられますね！
"

NewTactic rw
NewHiddenTactic nth_rw
DisabledTactic tauto
