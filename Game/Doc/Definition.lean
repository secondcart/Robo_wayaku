import GameServer.Commands

/-! ## 定義 -/


/- 写像 -/

/--
写像 `f` が単射（injective）であるとは, 次が成り立つこと：

```
∀ a b, f a = f b → a = b
```
-/
DefinitionDoc Function.Injective as "Injective"


/--
写像 `f` が全射（surjective）であるとは, 次が成り立つこと：

```
∀ b, ∃ a, f a = b
```
-/
DefinitionDoc Function.Surjective as "Surjective"


/--
写像が全単射（bijective）であるとは, 単射かつ全射であること.
-/
DefinitionDoc Function.Bijective as "Bijective"


/--
写像 `f` が狭義単調増加（strictly monotonic）であるとは, 次が成り立つこと：

```
∀ ⦃a b⦄, a < b → f a < f b
```
-/
DefinitionDoc StrictMono as "StrictMono"


/-- `Function.RightInverse f g` は `LeftInverse g f` として定義される.
つまり, `∀ x, g (f x) = x` を意味する.

残念ながら `RightInverse` ではなく `Function.RightInverse` と書く必要がある.
-/
DefinitionDoc Function.RightInverse as "RightInverse"


/--
`LeftInverse g f` は `g ∘ f = id`, より正確には：
`∀ x, g (f x) = x` を意味する.
-/
DefinitionDoc Function.LeftInverse as "LeftInverse"


/--
`HasRightInverse f` は, `f` が右逆写像を持つことを意味する.

`HasLeftInverse f` は, `f` が左逆写像を持つことを意味する.
-/
DefinitionDoc Function.HasRightInverse as "Has…Inverse"


/--
自己写像 `f : A → A` と元 `a : A` に対して, `IsFixedPt f a` は `f a = a` という主張.
-/
DefinitionDoc Function.IsFixedPt as "IsFixedPt"

/--
写像 `f : A → A` に対して, `fixedPoints f : Set A` は `f` の不動点の集合.
-/
DefinitionDoc Function.fixedPoints as "fixedPoints"

/--
部分集合 `A` と `B`（`A B : Set S`）に対して, `A ∪ B` はそれらの和集合.
-/
DefinitionDoc Set.union as "∪"

/--
部分集合 `A` と `B`（`A B : Set S`）に対して, `A ∩ B` はそれらの共通部分.
-/
DefinitionDoc Set.inter as "∩"

/--
写像 `f : A → B` に対して, `range f` は `f` の像全体：
```
range f = {f a | a : A}
        = {  b | ∃ a, f a = b}
```
-/
DefinitionDoc Set.range as "range"

/--
写像 `f : A → B` に対して, `image f : Set A → Set B` は
部分集合に対する誘導写像で, `A` の部分集合を `f` による像に写す.
-/
DefinitionDoc Set.image as "image"

/--
写像 `f : A → B` に対して, `preimage f : Set B → Set A` は
部分集合に対する誘導写像で, `B` の部分集合を `f` による逆像に写す.
-/
DefinitionDoc Set.preimage as "preimage"


/--
写像 `f : A → B` と部分集合 `S`（`S ⊆ A`）に対して,
```
f '' S = {f a | a ∈ S}
       = {b | ∃ a ∈ S, f a = b}
```
は `f` による `S` の像.
-/
DefinitionDoc Set.fimage as "f ''"

/--
写像 `f : A → B` と部分集合 `T`（`T ⊆ B`）に対して,
```
f ⁻¹' T = { a | f a ∈ T}
```
は `f` による `T` の逆像.
-/
DefinitionDoc Set.fpreimage as "f ⁻¹'"

/--
`fun x ↦ _` は無名関数を定義する記法.
例えば `fun (x : ℤ) ↦  -x` は `ℤ → ℤ` の否定を定義する.
-/
DefinitionDoc Symbol.function as "fun x ↦ _"


/- 集合 -/

/-- `A : Set T` は `A` が `T` の部分集合であることを意味する.
-/
DefinitionDoc Set as "Set"

/-- 部分集合 `A : Set T` と元 `a`（型 `T`）に対して, `a ∈ A` は
`a` が `A` に属することを意味する.
-/
DefinitionDoc Mem as "∈"

/-- 述語 `P : T → Prop` に対して, `{ a : T | P a } : Set P` は
`P` を満たす元からなる部分集合.
-/
DefinitionDoc setOf as "{·|·}"

/-- 部分集合 `A, B : Set T` に対して, `A\B` は `A` と `B` の差集合.
-/
DefinitionDoc SDiff as "·\\·"

/--
部分集合 `A, B : Set T` に対して, `A ⊆ B` は `A` が `B` に含まれることを意味する.
-/
DefinitionDoc Subset as "⊆"

/-- `∅ : Set T` は空集合.
-/
DefinitionDoc Set.empty as "∅"

/-- `univ : Set T` は型 `T` の全ての元からなる部分集合.
-/
DefinitionDoc Set.univ as "univ"

/-- 有限部分集合 `A : Finset T` と元 `a : T` に対して,
`insert a A` は `A ∪ {a}` の別表記.
-/
DefinitionDoc Finset.insert as "insert"

/-- 有限部分集合 `A : Finset T` と元 `a : T` に対して,
`erase A a` は `A \ {a}` の別表記.
-/
DefinitionDoc Finset.erase as "erase"

/-- 有限部分集合 `A : Finset T` に対して, `card A : ℕ` は `A` の要素数.
-/
DefinitionDoc Finset.card as "card"

/-- `n : ℕ` に対して, `Fin n` は集合 $\{0, \dots, n-1\}$.
-/
DefinitionDoc Fin as "Fin"

/-- `Nonempty T` は型 `T` に元が存在することを意味する.
-/
DefinitionDoc Nonempty as "Nonempty"

/-- 部分集合 `A : Set T` に対して, `Set.Finite A` は `A` が有限集合であることを意味する.
-/
DefinitionDoc Set.Finite as "Set.Finite"


/- 論理 -/

/-- `(A : Prop)` は真偽が定まらない命題.
-/
DefinitionDoc «Prop» as "Prop"

/--
`A ∧ B` は `A` と `B` がともに真である命題.
-/
DefinitionDoc And as "∧"

/--
`A ∨ B`（「または」）は `A` または `B` の少なくとも一方が真である命題.
-/
DefinitionDoc Or as "∨"

/--
`A → B` は「`A` ならば `B`」という含意.
-/
DefinitionDoc Arrow as "→"

/-- `A ↔ B` は `A` と `B` が同値であることを意味する.
-/
DefinitionDoc Iff as "↔"

/-- 存在量化子：`P : A → Prop` に対して,
`∃ a : A, P a` は `P a` を満たす `a` が存在することを意味する.
-/
DefinitionDoc Exists as "∃"

/-- 一意存在量化子：`P : A → Prop` に対して,
`∃! a : A, P a` は `P a` を満たす `a` が唯一存在することを意味する.
-/
DefinitionDoc ExistsUnique as "∃!"

/-- 全称量化子：`P : A → Prop` に対して,
`∀ a : A, P a` は全ての `a` で `P a` が成り立つことを意味する.
-/
DefinitionDoc Forall as "∀"


/-- `True : Prop` は常に真な命題.
-/
DefinitionDoc True as "True"

/-- `False : Prop` は常に偽な命題.
-/
DefinitionDoc False as "False"

/-- `¬ A` は `A` の否定.
-/
DefinitionDoc Not as "¬"

/--
等式に関する有用なtactic：`rfl`, `rw`, `trans`
-/
DefinitionDoc Eq as "＝"

/--
不等式 `x ≠ y` は `¬ x = y` として定義される.
-/
DefinitionDoc Ne as "≠"


/- 自然数 -/

/-- `Even n` は `n : ℕ` が偶数であるという主張：
```
∃ r : ℕ, n = r + r
```
-/
DefinitionDoc Even as "Even"

/-- `Odd n` は `n : ℕ` が奇数であるという主張：
```
∃ k : ℕ, n = 2 * k + 1
```
-/
DefinitionDoc Odd as "Odd"

/--
`n : ℕ` に対して, `Prime n` は `n` が素数であることを意味する.
-/
DefinitionDoc Nat.Prime as "Prime"

/--
`succ : ℕ → ℕ` は `n ↦ n + 1` という写像.
-/
DefinitionDoc Nat.succ as "succ"

/--
`n : ℤ`（非負整数）に対して, `n.toNat : ℕ` は同じ値を自然数として表す.
-/
DefinitionDoc toNat as "toNat"

/- その他 -/

/-- `x : ℝ` に対して, `|x|` は `x` の絶対値.
-/
DefinitionDoc absValue as "|・|"

/-- 有限添字集合 `I : Finset T` に対して, `∑ i ∈ I, f i` は和 $\sum_{i\in I} f(i)$.
 -/
DefinitionDoc Sum as "∑"

/-- 有限添字集合 `I : Finset T` に対して, `∏ i ∈ I, f i` は積 $\prod_{i\in I} f(i)$.
 -/
DefinitionDoc Prod as "∏"

/-- `P : MvPolynomial (Fin n) R` は `n` 変数多項式を表す.
-/
DefinitionDoc MvPolynomial as "MvPolynomial"
