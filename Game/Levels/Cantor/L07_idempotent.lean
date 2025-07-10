import Game.Metadata
import Game.Levels.Cantor.L06_IsFixedPt_odd

World "Cantor"
Level 7

Title ""

Introduction ""

Conclusion "
  **カントール**: おや, もう終わったのかい？？

  **Robo**: まだメモが1枚残ってるよ。
"

open Function Set

/-
  planned to be used as `range_fixedPoints` for future planet on quotients;
  don't need a name for now
-/
Statement {A : Type} (f : A → A) (h : f ∘ f = f) :
    range f = fixedPoints f := by
  Hint "
    **Robo**: まずは全ての定義を書き出すことから始めるのがいいよ。
    `unfold range fixedPoints IsFixedPt`って感じで。
    仮定`{h}`は`congr_fun`で詳しく展開できるんじゃないかな。
    "
  unfold range fixedPoints IsFixedPt
  Hint (hidden := true) (strict := true) "
    **Robo**: `apply congr_fun at h`ってやるつもりだったんだ。
  "
  apply congr_fun at h
  Hint (hidden := true) (strict := true) "
    **Robo**: まずは`ext`から始めてみたら？
    あるいは`Subset.antisymm_iff`でもいいかも。
    "
  Branch
    rw [Subset.antisymm_iff]
    simp
    constructor
    · assumption
    · intro a ha
      use a
  ext a
  simp
  constructor
  · intro ⟨y, hy⟩
    rw [← hy]
    specialize h y
    clear hy
    Hint (hidden := true) "**Robo**: `comp_apply`が役立つかも？あるいは`simp`？"
    simp at h -- or: rw [comp_apply] at h
    assumption
  · intro ha
    use a


TheoremTab "Function"
