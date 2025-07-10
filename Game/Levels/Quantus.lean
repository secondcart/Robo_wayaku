import Game.Levels.Quantus.L01_NonemptyUse
import Game.Levels.Quantus.L02_NonemptyObtain
import Game.Levels.Quantus.L03_Decide
import Game.Levels.Quantus.L04_Exists
import Game.Levels.Quantus.L05_neg_pow
import Game.Levels.Quantus.L06_odd_iff_not_even
import Game.Levels.Quantus.L07_Forall
import Game.Levels.Quantus.L08_PushNeg
import Game.Levels.Quantus.L09_PushNeg
import Game.Levels.Quantus.L10_DrinkersParadox

/-!
The planet `Quantus` is about the quantifiers `∀` and `∃`.
-/

World "Quantus"
Title "Quantus"

Image "images/Quantus.png"

Introduction "クアンタスでは, すでに大勢の形式哲学者たちが待ち構えています. 
彼らは皆が一斉に騒ぎ立て, あなたは声をかけることさえ難しい状況です. 
Roboがついに大きなゴングの音を鳴らし, 一時的に静寂をもたらします. 

**あなた**: 女王様への手紙を持ってきました. 女王様のもとへ案内していただけませんか？

**全員** *(合唱のように)*: 私たちはもう全員ここにいます！

**あなた**: わかりました. では, どなたが女王様ですか？

すると気まずい沈黙が訪れます. 全員が肩をすくめます. 

**あなた**: そもそも女王様はいるんですか？

**全員** *(合唱のように)*: はいはい. 女王様はいます, 女王様はいます. 

**Robo** *(あなたに)*: 要約しましょう. 女王は存在するが, 誰もその正体を知らない…

**あなた**: それって矛盾してませんか？

**Robo**: 数学者である君が聞くこと？ いいえ, 矛盾ではありません. これは単なる「純粋な存在命題」です. 

あなたは彼が本気で言っているのか少し不安になります. 

**あなた**: それなら, 荷物は全住民に渡すことにしましょう. そうすれば女王様にも渡したことになりますから. 

**あなた** *(群衆に向かって)*: インプリスから皆さんへの荷物です. どうぞ, これが贈り物です. 

Roboが群衆に投げると, 形式哲学者たちはそれを開封します. 
中には実際, たった1枚の紙きれしか入っていません. 
数分後, それは再びあなたたちの手元に戻ってきます. 
そして形式哲学者たちは皆, あなたたちがどう対応するか興味津々で見つめています. 
"
