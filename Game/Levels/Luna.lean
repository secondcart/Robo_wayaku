import Game.Levels.Luna.L01_le_rfl
import Game.Levels.Luna.L02_Omega
import Game.Levels.Luna.L03_Linarith__lt_trichotomy
import Game.Levels.Luna.L04_Omega2
import Game.Levels.Luna.L05_Linarith2
import Game.Levels.Luna.L06_Icc__Icc_insert_succ_right
import Game.Levels.Luna.L07_Linarith2
import Game.Levels.Luna.L08_Omega3
import Game.Levels.Luna.L09_lt_trichotomy2
import Game.Levels.Luna.L10_Icc_subset_Icc_iff

/-!
The planet Luna is about inequalities `≤` and the tactics `omega` (for ℕ) and `linarith` (for ℝ).
-/

World "Luna"
Title "Luna"

Image "images/MoonLuna.png"

Introduction "
Roboは小さな月を発見し, そこへ向かっています. 
表面はとても滑らかですが, 一部に小さな開口部があり, 階段が内部へ続いています. 
着陸して好奇心から降りていくと, 今まで見た中で最も整頓された住居にたどり着きます. 
小さな女の子が皆を迎えます. 

**リナ**: 私はリナ, ルナの唯一の住人よ. 

彼女はRoboを見ます. 

**リナ**: まあ, 実際はここには2人いるんだけど…

振り返って何か叫ぶと, スマートエルフがやってきます. 

**リナ**: これはリサよ! 

Roboは明らかに彼女を可愛いと思っています. 

**リナ**: でも, こんなところで散らかって立たないで! 靴とヘルメットはあそこに片付けて, 
それから訪問者用のマークされた場所に立ってね. じゃないと, 私が混乱しちゃうわ. 

"
