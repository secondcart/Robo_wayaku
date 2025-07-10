import Game.Metadata


World "Vieta"
Level 9

Title "" -- "congr_fun"


Introduction ""


open Function

Statement (f g : ℤ → ℤ) (h : f = g) (x : ℤ) : f x = g x := by
  Hint "
**Robo**: これは`congr_fun`のケースです。
    `h : f = g`という仮定がある場合, `apply congr_fun at h`を使って`h : ∀ x, f x = g x`に書き換えることができます。

**あなた**: でも, ここではもっと簡単に`rw [h]`を使うこともできるのでは？

**Robo**: はい, この単純な例では確かにそうです。しかし, `f`がより複雑な式で, 証明目標に正確に現れていない場合は使えません。
私が言った通りに試してみてください。
  "
  apply congr_fun at h
  Branch
    specialize h x
    assumption
  apply h

/---/
TheoremDoc congr_fun as "congr_fun" in "Function"

OnlyTactic apply assumption «have»
NewTheorem congr_fun
TheoremTab "Function"

Conclusion ""
