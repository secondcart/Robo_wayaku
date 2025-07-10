import Game.Metadata


World "Vieta"
Level 7

Title "Verzweigung"

Introduction "
遠くから戦闘音が聞こえてきます. Vietaは相変わらず動じていないようです. 
彼はあなたにさらなる課題を与えます. 
"

open Function Set Nat

Statement {A : Type} (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n : ℕ, (f n = g n) := by
  Hint "
    **Robo**: おそらくここでは`toNat`が必要でしょう: `n : ℤ`が整数の場合, 
       `n.toNat : ℕ`は同じ数ですが, 自然数として扱われます. 

    **あなた**: え? 例えば`(-1).toNat`は何になるの? 

    **Robo**: 分かりません. 私が言いたかったのは, *`n ≥ 0`の場合*, 
               `n.toNat`は依然として「同じ」数だということです. 
    "
  Hint (hidden := true) "**Robo**: `if 0 ≤ n then ... else ...`を使って区分的に関数を
  定義できます. "
  let g : ℤ → A := fun n ↦ if (0 ≤ n) then f n.toNat else f 0
  Hint (strict := true) "**Robo**: これで`use`を使って`g`を適用し, 
  あなたの定義が良かったか確認できます. "
  use g
  intro n
  simp [g] -- TODO: There's a tiny bit magic in this step.


NewDefinition toNat


NewTactic  «if»
NewHiddenTactic «then»  «else»
