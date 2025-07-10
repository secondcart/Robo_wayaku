import Game.Levels.Robotswana.L01_SMulEBasis

World "Robotswana"
Level 2

Title "Falsche Indizes"

Introduction
"
少し時間が経つと, あなたは2枚の非常に似たメモを見つけます. 
またしても落書きだらけで, ほとんどすべてが線で消されています. 
しかし, それぞれの最初の行だけはかろうじて読み取れます. 
"

Conclusion "
  **Robo**: この`E.mul_of_ne`も保存しておこう, いつか役に立つかもしれない. 

  **あなた**: でも今は, 誰がこれらのメモをここに落としたのか, あるいは捨てたのか気になってきた. さあ, 先に進もう. 
"

open Nat Matrix

/---/
TheoremDoc Matrix.E.mul_of_ne as "E.mul_of_ne" in "Matrix"

-- @[inherit_doc Matrix.StdBasisMatrix.mul_of_ne]
Statement Matrix.E.mul_of_ne {n : ℕ} (i j : Fin n) {k l : Fin n} (h : j ≠ k) : E i j * E k l = 0 := by
  Hint "**あなた**: これは行列の乗算のように見える. 
  これで正しいはずだ. 
  "
  unfold E
  Hint (hidden := true) "**Robo**: ただし, `simp`は仮定`{h}`を明示的に必要とすることを忘れないで！"
  simp [h]

TheoremTab "Matrix"
