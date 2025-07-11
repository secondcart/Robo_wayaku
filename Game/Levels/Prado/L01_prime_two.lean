import Game.Metadata

World "Prado"
Level 1

Title ""

Introduction "**Robo**: はは, そうだね. 私たちは知っている. 

彼は素早くLeanの言語で声明を書き上げ, あなたに差し出した. 
"

/---/
TheoremDoc Nat.prime_two as "prime_two" in "ℕ"

namespace Nat

Statement prime_two : Prime 2 := by
  Hint "**Robo** *(囁きながら)*: これはとても簡単だよ. `2`は具体的な数字で, 
  素数かどうかを判定するアルゴリズムがあるから, `decide`を使うだけでいいんだ! "
  decide

TheoremTab "ℕ"

Conclusion "
**あなた**: 確かに. 私たちは知っている. 他にどんな展示物があるの? 

Guinoは少し照れくさそうになる. 

**Guino**: ええ, そうですね, 私たちはオープンしたばかりで. 
そして最初は最も美しい素数だけを展示することにしたんです：
偶数です. 現在, `2`が私たちの唯一の展示物です. 
でも, 常設展示のためにさらに他の偶数の素数を見つけるべく全力で取り組んでいます. "

NewDefinition Nat.Prime
