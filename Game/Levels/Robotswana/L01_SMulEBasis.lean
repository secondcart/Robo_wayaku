import Game.Metadata
import Game.Levels.Babylon

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Robotswana"
Level 1

Title "Standardbasis"

Introduction
"
足跡をたどると, 羊皮紙の一片が見つかりました. 上部にはメモが書かれています. 

```
E i j := stdBasisMatrix i j (1 : ℝ)
```

その下には少し乱暴な走り書きがありますが, 最初の行ははっきりと書かれています:
"

open Nat Matrix

def Matrix.E {n : ℕ} (i j : Fin n) : Mat[n,n][ℝ] :=
  stdBasisMatrix i j (1 : ℝ)

/-- `E i j` ist die `n × n`-Matrix (mit Werten in `ℝ`) mit einer `1` an
Stelle $(i, j)$ und Null überall sonst.

Dies ist eine spezialisierte Form der generellen `stdBasisMatrix i j (a : R)`,
welche auch nicht-quadratisch sein kann und einen beliebigen Wert `a` aus einem beliebigen
Ring annehmen kann. Wir benutzen hier `E` einfach als Abkürzung.
-/
DefinitionDoc Matrix.E as "E"

/---/
TheoremDoc Matrix.smul_ebasis as "smul_ebasis" in "Matrix"

Statement Matrix.smul_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) (i j) :
    A i j • E i j = stdBasisMatrix i j (A i j) := by
  Hint "**あなた**: ここに足跡を残した存在が何であれ, 行列が好きなようです. 
  とにかく, `Mat[{n},{n}]`は$({n} \\times {n})$行列のように見えます. 
  ただ, `Fin {n}`が何か思い出せません. 

  **Robo**: `Fin {n}`は集合$\\\{0,...,n-1\\}$です. 
  行と列のインデックスはここでは1ではなく0から始まります. 
  そして`stdBasisMatrix i j a`は偶然知っています. 
  これは位置`(i, j)`に要素`a`があり, 他はすべて0の行列です. 

  **あなた**: そして`E`は`a = 1`の場合の略記ですか? 

  **Robo**: その通りです. `A i j`は単に行列`A`の位置`(i, j)`の要素です. 

  **あなた**: ああ, 分かりました. つまりこれは行列の積ではなく, スカラー倍なのですね. こんな感じで...

  あなたは紙に走り書きします:

  $$
  A_\{i,j} \\cdot
  \\begin\{pmatrix}
  0 & 0 & 0\\
  1 & 0 & 0 \\
  0 & 0 & 0
  \\end\{pmatrix}
  =
  \\begin\{pmatrix}
  0 & 0 & 0\\
  A_\{i,j} & 0 & 0 \\
  0 & 0 & 0
  \\end\{pmatrix}
  $$

  **あなた**: それならこれはまた...自明ですね！? 

  **Robo**: はい. `unfold E`から始めれば, 残りは自然に進むと思います. 
  "
  unfold E
  simp

Conclusion "**あなた**: そしてこの「発見」をどうするつもりですか? 

**Robo**: 分かりません. とりあえず`Matrix.smul_ebasis`として保存しておきましょう, また必要になるかもしれません. 

こうしてあなたたちは足跡をさらに追っていきます. 
"
NewDefinition Matrix.E

TheoremTab "Matrix"
