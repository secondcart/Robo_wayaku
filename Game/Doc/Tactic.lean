import GameServer.Commands

/--
`apply`を使用すると, 含意`hAB : A → B`を適用できます：

| 前          | tactic       | 後                  |
|:------------|:----------------|:-------------------|
| `⊢ B`       | `apply hAB`     | `⊢ A`              |
| `h : A`     | `apply hAB at h`| `h : B`            |

どちらの場合も, 含意`hAB`は仮定として与えられるか, 既知の補題として使用できます.
-/
TacticDoc apply

/--
`assumption`は, 仮定の1つが証明目標と完全に一致する場合に証明を完了します.
-/
TacticDoc assumption

/--
tactic`by_cases h : P`は, `P`が真か偽かの場合分けを開始します.
例えば, `by_cases h : a = b`は`a = b`と`a ≠ b`の場合に分けます.

証明目標は複製され, 最初の「コピー」には仮定`(h : P)`が追加され,
2番目の「コピー」には仮定`(h : ¬P)`が追加されます.
-/
TacticDoc by_cases

/--
tactic`by_contra h`は矛盾による証明を開始します.
現在の証明目標が`P`の場合, `by_contra h`は新しい仮定`(h : ¬P)`を生成し,
証明目標を`False`に設定します.

## 関連tactic
* 矛盾証明の最後には通常`contradiction`が使用されます：
  このtacticは, 明らかに矛盾する2つの仮定を見つけた場合に証明を完了します.
* 証明目標が`A → B`の形式の場合, `contrapose`を使用して対偶による証明を開始できます.
-/
TacticDoc by_contra

/--
`change t`は証明目標を`t`に変更します. 前提として, `t`と古い証明目標が定義的に等しい必要があります.
これは特に, tacticが証明目標が実際に必要な項と定義的に等しいことを認識しない場合に役立ちます.

## 例
現在の証明状況：
```
b: ℝ
⊢ 1 • b = b
```
スカラー乗算が`fun (a : ℚ) (r : ℝ) => ↑a * r`と定義されている場合,
`change (1 : ℚ) * b = b`で証明目標を書き換え, その後乗算に関する補題で証明できます.
-/
TacticDoc change

/--
`h : ∃ (b : B), P b`の形式の仮定は,
`choose b hb using h`で`b : A`と`hb : P b`に分解できます.

より一般的に, `choose`を使用して選択公理で要素を選択できます：
`h : ∀ (a : A), ∃ (b : B), P a b`の形式の仮定から,
`choose f hf using h`は写像`f : A → B`と仮定`hf : ∀ (a : A), P a (f a)`を抽出します.
-/
TacticDoc choose

/--
`constructor`は証明目標を構成要素に分割します.

| 前          | 後                  |
|:------------|:-------------------|
| `⊢ A ∧ B`   | `⊢ A`と`⊢ B`       |
| `⊢ A ↔ B`   | `⊢ A → B`と`⊢ B → A` |

## 関連tactic
* 仮定は`obtain`で構成要素に分解できます.
* `A ∨ B`を証明するには, `left`または`right`でどちらかを選択する必要があります.
-/
TacticDoc constructor

/--
`contradiction`は, 仮定に矛盾がある場合に証明を完了します.
矛盾は例えば以下のように見えます：

* `h : n ≠ n`
* `h : A`と`h' : ¬A`
* `h : False`

## 関連tactic
通常, `contradiction`は`by_contra`で開始された矛盾証明を完了するために使用されます.
-/
TacticDoc contradiction

/--
tactic`contrapose`は`A → B`の形式の証明目標を`¬B → ¬A`に変更し,
対偶による証明を開始します.

## 関連tactic
`revert h`は`contrapose`を使用する前に仮定を含意の前提として記述するのに役立ちます.
-/
TacticDoc contrapose

/--
tactic`exact h`は, 項`h`が証明目標と一致する場合に証明を完了します.
-/
TacticDoc exact

/--
与えられた集合の2つの部分集合は, 同じ要素を持つ場合に等しいです.
証明目標に`A = B`（`A B : Set T`）がある場合,
`ext x`は証明目標を`x ∈ A ↔ x ∈ B`に変換します.
-/
TacticDoc ext

/--
`fin_cases i`は, `i`が有限型の場合に場合分けを実行します.

## 詳細
`fin_cases i`は特に`(i : Fin n)`に対して有用で,
有限次元ベクトル空間のインデックスとして使用できます.
-/
TacticDoc fin_cases

/--
同じ値域と定義域を持つ2つの関数は,
定義域のすべての要素で同じ値を取る場合に等しいです.
`f = g`（`f g : X → Y`）の形式の証明目標は,
`funext x`で`f x = g x`に変換されます.
-/
TacticDoc funext

/--
`generalize`は証明目標を一般化できます:
例えば, `generalize h : a = b`は証明目標のすべての`a`を`b`に置き換えます.

## 例
`Even x ∨ ¬Even x`の目標は,
`generalize h : (Even x) = A`で`A ∨ ¬A`に変換できます.
-/
TacticDoc generalize

/--
`have h : P`は中間結果を導入します.
その後, この中間結果を証明してからメインの証明を続行します.

## 関連tactic
`suffices h : P`も同様ですが, まずメインの証明を続行し,
最後に中間結果を証明します.
-/
TacticDoc «have»

/--
`if … then … else`を使用して, 2つの定義分岐を持つ関数を定義できます.

## 関連tactic
* `h : A`がある場合, `rw [if_pos h]`で`if A then B else C`を`B`に簡約できます.
* `h : ¬ A`がある場合, `rw [if_neg h]`で`if A then B else C`を`C`に簡約できます.
-/
TacticDoc «if»

/--
tactic`induction n`は`n`に関する帰納法による証明を実行します.
`induction n with d hd`で帰納変数（`d`）と帰納仮定（`hd`）に名前を付けられます.

## ゲーム内の変更
ゲーム外では, `induction`は`induction'`と呼ばれ,
`0`は`Nat.zero`, `d + 1`は`Nat.succ d`と書かれます.
-/
TacticDoc induction

/--
tactic`intro`は`A → B`または`∀ x, P x`の証明目標に使用されます.

| 前          | tactic     | 後                  |
|:------------|:-------------|:-------------------|
| `⊢ A → B`   | `intro h`    | `h : A`, `⊢ B`     |
| `⊢ ∀ x, P x`| `intro x hx` | `x : X`, `hx : P x`|

## 関連tactic
`revert h`は`intro h`の逆を行います.
-/
TacticDoc intro

/--
証明目標が`A ∨ B`の場合, `left`で左側を示すことを選択します.

## 関連tactic
`right`で右側を選択できます.
-/
TacticDoc left

/--
`let`は一時的な定義を導入します:
例えば, `let x : ℕ := 5 ^ 2`です.
-/
TacticDoc «let»

/--
`linarith`は, 与えられた等式や不等式から線形の等式や不等式が導かれることを示せます.
-/
TacticDoc linarith

/--
`omega`は, `ℕ`または`ℤ`における線形の等式や不等式が,
与えられた等式や不等式から導かれることを示せます.
-/
TacticDoc omega

/--
`push_neg`は否定を量化子の前に移動します：

| 前          | 後              |
|:------------|:---------------|
| `¬∀ x, P x` | `∃ x, ¬P x`    |
| `¬∃ x, P x` | `∀ x, ¬P x`    |

## 関連tactic
`not_forall`と`not_exists`は`rw`で個別に適用できます.
-/
TacticDoc push_neg

/--
`obtain`は仮定を構成要素に分解します.

| 前                | tactic               | 後                          |
|:------------------|:-----------------------|:---------------------------|
| `h : A ∧ B`       | `obtain ⟨h₁, h₂⟩ := h` | `h₁ : A`, `h₂ : B`          |
| `h : A ↔ B`       | `obtain ⟨h₁, h₂⟩ := h` | `h₁ : A → B`, `h₂ : B → A`  |
| `h : Nonempty X`  | `obtain ⟨x⟩ := h`      | `x : X`                     |
| `h : ∃ x : X, P x`| `obtain ⟨x, hx⟩ := h`  | `x : X`, `hx : P x`         |
| `h : A ∨ B`       | `obtain h | h := h`   | `h : A`または`h : B`の目標  |
-/
TacticDoc obtain

/--
`refine' { .. }`は構造体（例：$R$-加群）をtacticモードで個々の証明目標に分割するために必要です.
-/
TacticDoc refine'

/--
tactic`revert h`は仮定`h`を含意の前提として証明目標に追加します.

## 関連tactic
`intro h`は`revert h`の逆を行います.
-/
TacticDoc revert

/--
`rfl`は`X = X`を証明します. 正確には, `A`と`B`が定義的に等しい場合に`A = B`を証明します.
-/
TacticDoc rfl

/--
証明目標が`A ∨ B`の場合, `right`で右側を示すことを選択します.

## 関連tactic
`left`で左側を選択できます.
-/
TacticDoc right

/--
tactic`ring`は`+, -, *, ^`の操作を含む等式を半環（特にℕ, ℤ, ℚ, ℝ）で証明します.
-/
TacticDoc ring

/--
等式`h : X = Y`または同値`h : X ↔ Y`がある場合, `rw [h]`で証明目標の`X`を`Y`に置き換えられます.

## バリエーション
* `rw [←h]`は`h`を逆に適用し, `Y`を`X`に置き換えます.
* `rw [h] at h₂`は仮定`h₂`で置換を行います.
* `nth_rw k [h]`は`k`番目の出現を置換します.
-/
TacticDoc rw

/--
tactic`simp`は多くの補題を適用して式を簡約します.

## バリエーション
* `simp [h]`は追加で仮定`h`を使用します.
* `simp only [h,f,g]`は`h`, `f`, `g`のみを使用します.
-/
TacticDoc simp

/--
`simp_rw [h₁, h₂, h₃]`は各補題を可能な限り適用しますが, `rw`よりも量化子の下でうまく機能します.
-/
TacticDoc simp_rw

/--
`specialize h a₁ a₂`は`have h := h a₁ a₂`と同等です：仮定`h : ∀ m₁ m₂, P m₁ m₂`を`h : P a₁ a₂`に置き換えます.
-/
TacticDoc specialize

/--
`suffices h : P`は, 証明目標が`P`から導かれることを示す証明セクションを開始します.
その後, `P`を証明します.

## 関連tactic
`have h : P`も同様ですが, まず`P`を証明してからメインの証明を続行します.
-/
TacticDoc «suffices»

/--
tactic`symm`は証明目標の等式（`=`）または同値（`↔`）の両側を交換します.

## バリエーション
* `symm at h`は仮定`h`で操作します.
* `h.symm`は`symm at h`の結果です.
-/
TacticDoc symm

/--
`trans`は等式または同値に中間ステップを挿入します:

| 前          | 後                  |
|:------------|:-------------------|
| `⊢ A = C`   | `⊢ A = B`と`⊢ B = C`|
| `⊢ A ↔ C`   | `⊢ A ↔ B`と`⊢ B ↔ C`|
-/
TacticDoc trans

/--
`decide`は単純なアルゴリズムで決定可能な命題を証明します.
例えば：
- `Even 4`
- `2 ≤ 5`
- `4 ≠ 6`
- `Prime 7`
-/
TacticDoc decide

/--
`unfold F`は証明目標で定義`F`を展開します.
`unfold F at h`は仮定`h`で同じことを行います.

## 関連tactic
`unfold F`と`simp only [F]`はほぼ同じです.
-/
TacticDoc unfold

/--
証明目標が`∃x, P x`の場合, `use n`で具体的な要素を指定できます.
-/
TacticDoc use

/--
`tauto`はトートロジーを証明します.

## 関連tactic
場合によっては, `generalize`で証明目標を抽象化する必要があります.
-/
TacticDoc tauto
