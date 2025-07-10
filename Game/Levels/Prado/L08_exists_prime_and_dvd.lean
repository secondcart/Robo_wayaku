import Game.Metadata
import Game.Levels.Prado.L07_dvd_mul

World "Prado"
Level 8

Title ""

Introduction
"ギーノを機嫌よくさせるため, Roboは慎重に, 
課題を出してくれないかと尋ねます. 
彼は前回の課題のバリエーションを提示しました. 
"

namespace Nat

Statement : ∃ p : ℕ, Prime p ∧ p ∣ 67280421310721 := by
  Hint "**あなた** *(Roboに向かって)*: ここで素因数は何かわかる？

  **Robo**: ううん. 

  Roboは考え込む. 

  **Robo**: でも別にいいじゃん. 具体的な因数を聞いてるわけじゃなくて, 
  ただ任意の素因数の存在を問うてるだけだし. これは自明だよ. 
  考えてみる…`exists_prime_and_dvd`が使える命題だと思う. 
  "
  apply exists_prime_and_dvd
  simp


/---/
TheoremDoc Nat.exists_prime_and_dvd as "exists_prime_and_dvd" in "ℕ"
NewTheorem Nat.exists_prime_and_dvd

TheoremTab "ℕ"

Conclusion "
  **ギーノ**: まあいい, 先に進もう. 見て, この素敵な階段！
  登っていこう！

  **あなた** *(Roboに向かって)*: ギーノに見せたい主張を今度は考えてみよう. 
  ちょうど1つの偶数が存在する…

  **Robo**: 待って！「ちょうど1つ」はまだ習ってないよ. 
"
