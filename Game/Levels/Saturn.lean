import Game.Levels.Saturn.L01_Rewrite_equality
import Game.Levels.Saturn.L02_Ring_add_pow_two
import Game.Levels.Saturn.L03_mul_comm
import Game.Levels.Saturn.L04_mul_assoc
import Game.Levels.Saturn.L05_Ring

/-!
The planet `Saturn` introduces the tactics `ring` and `rw`.
-/

World "Saturn"
Title "Saturn"

Image "images/Planets/Planet_Orange.png"

Introduction "実はこの惑星には行きたくなかったのです.
しかし, あなたは気が散っていました.
宇宙では注意を怠ってはいけません, 特に不慣れな場所では尚更です.
もう近づきすぎていて, 重力が強すぎます. 再生可能なエンジンも現在は再生モード中です.

**あなた** この惑星のオレンジ色の液体は何だ?

**Robo** 毒々しいですね. あるいは熱いのかも.

**あなた** あるいは両方か. 本当に着陸したくない!

**Robo** はいはい, 最善を尽くしています. 見てください, 軌道上にどれだけのゴミが浮かんでいることか!
今できる最善のことは, 流れに身を任せることです.
"
