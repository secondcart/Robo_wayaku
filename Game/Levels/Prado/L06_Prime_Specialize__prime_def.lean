import Game.Metadata
import Game.Levels.Prado.L05_not_dvd_of_between_consec_multiples

World "Prado"
Level 6

Title ""

Introduction "
**あなた**: よし。それで, 素数をどう扱うか教えてくれる？

**ロボ**: 素数に関する課題があるか見てみよう…これなんかどうかな？"


namespace Nat

Statement (a p : ℕ) (hp : Prime p) (h : 2 ≤ a) (ha : a ∣ p) : a = p := by
  Hint "
    **ロボ**: ここで`(hp : Prime p)`はもちろん`p`が素数であるという仮定だ。
    この仮定を使うには, `rw [prime_def] at hp`とするのがベストだよ。"
  Branch
    unfold Prime at hp
    Hint "**ロボ**: いや, それはやめた方がいい。`Prime`をunfoldしないで！
    そうすると全てが難しくなるだけだ。私が言ったように`rw [prime_def] at hp`を使うんだ。"
  rw [prime_def] at hp
  Hint "**あなた**: なるほど。素数とは2以上の自然数で, 1と自分自身でのみ割り切れる数なんだ。聞き覚えがあるな。"
  obtain ⟨hp₁, hp⟩ := hp
  Hint "
    **あなた**: 今度は`{hp}`を`{a}`に適用したいんだよね？

    **ロボ**: それなら`have hp' := {hp} {a}`と言えばいい。もしくはもっとエレガントに：
    `specialize {hp} {a}`。
  "
  Branch
    -- Marcus' solution
    have ha' : a ∣ p → a = 1 ∨ a = p
    · -- Hint "**Robo**:  Statt `have` könntest du hier übrigens auch `specialize {hp} {a}` verwenden."
      apply hp
    have ha'' : a = 1 ∨ a = p
    · apply ha'
      assumption
    obtain h1 | h2 := ha''
    linarith
    assumption
  Branch
    -- alternative to `specialize`
    have _hp := hp a ha
    -- Hint "**Robo**:  Statt `have` könntest du hier übrigens auch `specialize {hp} {a} {ha}` verwenden."
  specialize hp a ha
  obtain hp | hp := hp
  · Hint (hidden := true) "**ロボ**: `linarith`を試してみて。`{a} = 1`と`2 ≤ {a}`の矛盾を見つけてくれるはずだ。"
    linarith
  · assumption

NewTactic specialize
-- Wird hier en passant eingeführt.
-- Sollte in jedem Fall in Hints erwähnt werden,
-- sonst ist es verwirrend, dass die Taktik auf
-- einmal im Inventory erscheint.
/---/
TheoremDoc Nat.prime_def as "prime_def" in "ℕ"
NewTheorem Nat.prime_def
TheoremTab "ℕ"

Conclusion ""
