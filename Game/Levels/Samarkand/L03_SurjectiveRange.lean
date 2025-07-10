import Game.Levels.Samarkand.L02_ImageMap


World "Samarkand"
Level 3

Title "Range of Surjection"


Introduction ""

open Function Set

Statement {A B : Type} {f : A → B} : Surjective f ↔ range f = univ := by
  Hint "
    **Robo**: ここで`range f`は`f`の全画像集合です:
    ```
      range f = \{f a | a : A}
              = \{  b | ∃ a, f a = b}
    ```
    これは基本的に`f '' univ`の別の書き方です. 
    これを使うには`mem_range`が便利です:
    ```
    x ∈ range f ↔ ∃ a, f a = b
    ```
  "
  /-
  example : range f =  {b | ∃ a, f a = b} := by
    rfl

  example : range f =  {f a | a : A} := by
    rfl

  example : range f = f '' univ := by
    simp   -- (rfl fails)
  -/
  Hint (hidden := true)  "**Robo**: `consturctor`から始めてみましょう. "
  Branch
    symm
    apply eq_univ_iff_forall  -- will be introduced in PIAZZA (TODO)
  constructor
  · intro hf
    Hint (hidden := true) "
      **Robo**: また集合の等式を示す必要がありますね？つまり`ext`です. 
      "
    ext b
    Branch
      tauto
    constructor
    · tauto
    · intro
      rw [mem_range] -- not necessary but desirable for the user.
      apply hf
  · intro h
    intro b
    --Branch
    --  simpa [← h] using mem_univ b -- simpa tactic has not been introduced
    rw [← mem_range]
    rw [h]
    tauto

NewDefinition Set.range

/---/
TheoremDoc Set.mem_range as "mem_range" in "Function"

NewTheorem Set.mem_range

Conclusion "
  **アラプカ**: これもきれいですね. 

  **Robo**: ところで, あなたはこの惑星全体を絵で埋め尽くしたんですか？

  **アラプカ**: いいえ. これは世代を超えた課題です. 
  最初の模様要素は私の高祖祖父が刻みました. 
  実際に何世代遡ればいいのか正確には分かりません. 
  ましてや, 原初の模様がどこから来たのかなどなおさらです. 
"
