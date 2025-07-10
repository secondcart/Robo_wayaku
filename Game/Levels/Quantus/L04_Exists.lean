import Game.Metadata

World "Quantus"
Level 4

Title "Gerade/Ungerade"

Introduction
"
群衆からの「偶数」「奇数」の叫び声はまだ消えていません. そのため, 
Roboは再度定義を示してくれます：

```
def Even (n : ℕ) : Prop := ∃ r, n = r + r
```

そして

```
def Odd (n : ℕ) : Prop := ∃ r, n = 2 * r + 1
```

これであなたたちはさらに1枚の紙を受け取ります. 
"

open Nat

/-- Das Quadrat einer geraden Zahl ist gerade. -/
TheoremDoc Nat.even_square as "even_square" in "ℕ"

Statement Nat.even_square (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  Hint "
    **Robo**: 上で見たように, `Even {n}`は`r`が存在して`r + r = {n}`となることで定義されています. 
    この定義を`unfold Even at *`で開くとわかりやすいでしょう. 

    **あなた**: `decide`では? 

    **Robo**: `decide`は機能しません. `{n}`は具体的な数値ではなく任意の数だからです. 
    ここでは実際に作業が必要です! "
  Branch
    unfold Even
    Hint "
      Robo**: `unfold Even at h`も行うと状況がより明確になります. "
  unfold Even at *
  Branch
    clear h -- we do that so the hint gets displayed regardless of the presence of additional hyps.
    use n^2/2
    Hint "群衆から困惑したつぶやきが聞こえる. 

    **あなた**: 待って, なぜ`{n} ^ 2 / 2`が自然数になるの? 

    **Robo**: Leanでのℕ上の除算は常に切り捨てられます. `{n} = 1`の場合, 

    ```
    1 ^ 2 = (1 ^ 2) / 2 + (1 ^ 2) / 2
    ```

    これは計算すると`1 = 1 / 2 + 1 / 2 = 0 + 0`となり, 間違っています! "
  Hint "
    **あなた**: `{h}`から, `s`が存在して`s + s = {n}`となることがわかった...

    **Robo**: `choose s hs using {h}`で実際にこの`s`を導入できます. "
  choose s hs using h
  Hint "
    **あなた**: 今度は`n ^ 2 = r + r`となる適切な数`r`を見つける必要がある? 

    **Robo**: その通りです. 必要なら`let r := …`でこの数を準備できます. "
  Branch
    rw [hs]
    Hint "**Robo**: それも可能ですが, 実際に数を考える必要があります. "
  let r := 2 * s^2
  Hint "
    **Robo**: この数は良さそうです! あとは`use r`と言うだけです. 
    最初から`use 2 * s^2`と言っても構いません. 
  "
  use r
  Hint (hidden := true) "
    **あなた**: あ, そして`ring`! 

    **Robo**: ただし先に`rw`で`n`を`{s} + {s}`に置き換える必要があります. 
    `ring`だけではわからないからです. "
  rw [hs]
  ring

NewTactic unfold choose «let»
NewHiddenTactic «using»
-- `let` is introduced here only to avoid dependency of Vieta on Euklid
--  Those are the first two planets that really need `let`,
--  and introducing `let` there will create dependencies of all later planets
--  on *both* of these!

NewDefinition Even Odd

Conclusion "拍手! "
