import Game.Metadata


World "Epo"
Level 3

Title ""


Introduction ""

open Function

Statement {A B : Type} {f : A -> B} {g : B -> A} :
    RightInverse g f ↔ LeftInverse f g := by
  Hint "
  **あなた**: おそらくこれは, `g`が`f`の右逆元であることと, `f`が`g`の左逆元であることは同値だと言っているのでしょう. 

  **Robo**: その通りです. しかし私の記憶が正しければ, これはLeanでは定理というより`Function.RightInverse`の定義そのものです. 残念ながら実際には`RightInverse`と書く代わりに`Function.RightInverse`と書かなければなりません. なぜなら`RightInverse`はLeanでは曖昧な表現だからです. 
  "
  Branch
    unfold Function.RightInverse
    rfl
  tauto

TheoremTab "Function"
NewDefinition Function.RightInverse Function.LeftInverse
