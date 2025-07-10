import Game.Metadata

World "Saturn"
Level 3

Title ""

Introduction "また無線信号が届いた. "

namespace MvPolynomial
Statement (P : MvPolynomial (Fin 2) ℚ) : (X 0) * P = P * (X 0) := by
  Hint "
    **あなた**: あれ, ここでの`P`って何者? 

    **Robo**: `P`は「多変数多項式」で, 変数は`Fin 2`で番号付けされ, 係数は`ℚ`に属します. 

    **あなた**: `Fin 2`って何? 

    **Robo**: 2つの要素を持つ標準集合——$\\\{0,1\\}$です. 変数は`X 0`と`X 1`と呼ばれます. 

    **あなた**: でも実際は関係ないよね? 多項式環は可換だし! 

    **Robo**: その通りです. 
  "
  ring

Conclusion "
また👍をもらいました. 
"
NewTactic ring

/---/
TheoremDoc mul_comm as "mul_comm" in "+ *"

NewTheorem mul_comm
NewDefinition Fin MvPolynomial
