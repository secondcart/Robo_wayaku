import Game.Levels.Logo.L01_Tauto
import Game.Levels.Logo.L02_Rfl
import Game.Levels.Logo.L03_Assumption
import Game.Levels.Logo.L04_Assumption
import Game.Levels.Logo.L05_True
import Game.Levels.Logo.L06_Not
import Game.Levels.Logo.L07_Contradiction
import Game.Levels.Logo.L08_Contradiction
import Game.Levels.Logo.L09_Contradiction
import Game.Levels.Logo.L10_And
import Game.Levels.Logo.L11_And
import Game.Levels.Logo.L12_Or
import Game.Levels.Logo.L13_Or
import Game.Levels.Logo.L14_Summary

/-!
The planet `Logo` is about first-order-logic.
-/

World "Logo"
Title "Logo"

Image "images/QueenOfLogic.png"

Introduction "
あなたはパラレルワールドに迷い込んだ. どうやら帰る方法はないようだ.
ここに留まり, 適応するしかない.

ここには多くの小さな惑星がある. すべて居住可能で,
1日に最大7回の夕焼けも楽しめる. しかし, それらの惑星はすべてFormalosophという
奇妙な生物が住んでいる. 彼らは風変わりな数学的執着を持つ存在だ.
そして不運なことに, 何故かあなたが数学者だったという噂が広まっている.
彼らの尽きることない知識欲を満たさない限り, ここで安らぎを見つけることはできないだろう.

大きな問題が2つある：1つは, Formalosoph全員が, 深い数学的理解をもっていない.
もう1つは, 彼らは数学について「Lean語」という未知の方言でコミュニケーションをとる.

幸い, 小さなスマートエルフRoboもあなたと一緒に宇宙を移動してきた.
Roboもこの状況で望んでいたような数学の天才ではないが,
どうやらどこかでLean語を学んだようだ. これは非常に価値がある.
"
