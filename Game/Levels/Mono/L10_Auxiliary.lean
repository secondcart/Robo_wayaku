import Game.Levels.Mono.L09_InjOfHasLeftInv

World "Mono"
Level 10

Title ""

Introduction ""

open Function Set

-- Could be done much earlier; needed as a have statement in the Boss level
-- Presumably needs hints!!
Statement {A B : Type} [hA : Nonempty A] (f : A → B ) : ∀ b : B, ∃ a : A, f a = b ∨ ¬ ∃ a' : A , f a' = b   := by
  Hint "
    **Du**:  私たちは今クァンタスに戻ったの? とにかく：`a`が存在するか, 存在しないかのどちらかで, これはトートロジーのように見える. 

    **Robo**:  ゆっくり! 暗黙の括弧に注意する必要がある. もっと括弧を付けて書き直してみよう：
    ```
    ∀ b : B, ∃ a : A,
       ( f a = b   ∨   ¬ ∃ a' : A , f a' = b )
    ```
  "
  Hint (hidden := true) "
    **Robo**:  まず最初に`obtain`を使って`A`から何か要素を取得してみては? 
    要素が存在することはわかっているからね. 
  "
  obtain ⟨a₀⟩ := hA
  intro b
  Hint (hidden := true) "
    **Robo**:  さて, `by_cases`を使って`{b}`が原像を持つかどうかで場合分けしてみたらどうかな. 
  "
  by_cases hb : ∃ a' : A, f a' = b
  · obtain ⟨a,ha⟩ := hb
    use a
    left
    assumption
  use a₀
  right
  assumption
