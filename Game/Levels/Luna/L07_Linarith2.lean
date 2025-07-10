import Game.Metadata

World "Luna"
Level 7

Title ""

Introduction
"
**リナ**: `omega`はもう十分, 今度は私の番よ. 
"

Statement (x y : ℚ) (h₁ : 35/11 * y ≤ 35/2 - 22/21 * x) (h₂ : 8/9 * y ≤ x + 17/8) : y ≤ 34/7 := by
  Hint "**あなた**: これはまず縦に書き直す必要があるな. 与えられた条件は:

  $$
  \\begin\{aligned}
    \\tfrac\{35}\{11}\\cdot y &\\le -\\tfrac\{22}\{21}\\cdot x + \\tfrac\{35}\{2}  \\\\
    \\tfrac\{8}\{9} \\cdot y &\\le x + \\tfrac\{17}\{8}
  \\end\{aligned}
  $$

  そして証明すべきは:
  $$
  y ≤ \\tfrac\{34}\{7}
  $$

  Robo？？

  リナがニヤリと笑う. 
  "
  linarith

Conclusion "**あなた**: 悪くないね！"
