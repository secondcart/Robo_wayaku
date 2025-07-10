import Game.Metadata
import Game.Levels.Prado.L08_exists_prime_and_dvd

World "Prado"
Level 9

Title ""

Introduction "
**Robo**: でもそんなに難しくないよ. ほら, この問題を見てみて. 
"


namespace Nat

Statement {a b : ℕ} (ha : 0 < a) (h : a ∣ b) : ∃! (m : ℕ), a * m = b := by
  Hint "
  **あなた**: わかった - `∃! m, P(m)`は「P(m)が成り立つmがちょうど1つ存在する」という記法なんだね. 

  **Robo**: その通り. これは単に「(1) P(m)が成り立ち, (2) P(m')が成り立つ他の要素m'はすべてmと等しい」ようなmが存在すると定義されている. 
  最初のステップは適切なmを見つけて, `use _`を使うことだよ. "
  obtain ⟨w, hw⟩ := h
  use w
  Hint "**Robo**: 実際, `use`を`∃!`に適用すると少し混乱が生じる. 
  読みやすくするために, すぐ後に`simp`を使うのがベストだよ. "
  simp
  Hint "**Robo**: これで証明すべき2つの命題がある:(1) `{w}`が`a * {w} = b`を満たすこと, 
  (2) `{w}`がこの性質を持つ唯一の要素であること. "
  constructor
  · rw [hw]
  · Hint "
    **Robo**: 素晴らしい. では一意性についてだ. この補題`mul_eq_mul_left_iff`が役立つと思う:

    ```
    a * b = a * c ↔ b = c ∨ a = 0
    ```
    "
    intro y hy
    rw [hw] at hy
    /-
    Branch
      rw [Nat.mul_left_cancel_iff] at hy -- TODO: _root_.mul_left_cancel_iff takes priority
      · assumption
      · assumption
    -/
    rw [mul_eq_mul_left_iff] at hy  -- `mul_eq_mul_left_iff` also used in ROBOTSWANA!
    obtain h | h := hy
    · assumption
    · linarith

NewDefinition ExistsUnique

/---/
TheoremDoc mul_eq_mul_left_iff as "mul_eq_mul_left_iff" in "+ *"
/---/
TheoremDoc mul_eq_mul_right_iff as "mul_eq_mul_right_iff" in "+ *"

TheoremTab "+ *"

NewTheorem mul_eq_mul_left_iff mul_eq_mul_right_iff

/-
/---/
TheoremDoc Nat.mul_left_cancel_iff as "mul_left_cancel_iff" in "ℕ"
/---/
TheoremDoc Nat.mul_right_cancel_iff as "mul_right_cancel_iff" in "ℕ"
NewTheorem Nat.mul_left_cancel_iff Nat.mul_right_cancel_iff
-/


TheoremTab "ℕ"
