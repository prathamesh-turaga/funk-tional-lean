import Mathlib

/-
## SECTION 1: EVALUATING EXPRESSIONS
`#eval` followed by an expression evaluates the expression. Place your cursor towards the end of the text of each line to see the output in the right panel (Infoview). Try to see the answer and guess if it corresponds to what you know.
-/

#eval 41 + 1

#eval "life, universe and everything"

#eval 1 = 42

#eval 1 ≠ 42

#eval [1, 2] = [1, 2]

#eval [1, 2] = [2, 1]

/-
**TO DO:** Check what happens when you do `#eval 1 ≠ [1, 2]` in the space below.
If you get an error message, what is it? What do you observe? Why?
-/


---

/-
## SECTION 2: FUNCTIONS
Lean is a functional programming language. Programs are essentially functions or compositions of functions. The following function `strange_add` takes two natural numbers `a` and `b`, and returns the number `2*a + b`.
-/

def strange_add (a b : ℕ) := 2 * a + b
-- `def` is the first part of the function definition syntax. We declare two input terms `a` and `b` and declare the output to be `2*a + b`.

-- This function can be evaluated as below. Note that we use spaces to separate arguments.
-- (If you're curious, look up "Currying" later!)

#eval strange_add 10 23

-- Defining more functions:
def cubic_exp (a b c d x : ℝ) :=
  a*x^3 + b*x^2 + c*x + d

def horner_exp (a b c d x : ℝ) :=
  ((a*x + b) * x + c)*x + d

-- **TO DO:** Write your own function below (keep it a simple polynomial).


---

/-
## SECTION 3: PROVING THEOREMS
Proving a theorem in Lean is essentially adopting a "backward proof." We reduce the main statement (called the **goal**) into simpler statements (newer goals) by invoking a `tactic`.

A `tactic` is a strategy that invokes existing theorems under the hood, using a deterministic algorithm that you won't be privy to in this tutorial. Our task is to apply tactics until no goals remain.
-/

/-
### The `ring` Tactic
The `ring` tactic invokes properties of addition, subtraction, and multiplication. It works on "Rings" (like Real numbers) and even "Commutative Semirings" (like Natural numbers).
-/

example (a b : ℝ) : a + b = b + a :=
  by ring

example (a b c : ℝ) : (b + a) + c = a + (b + c) :=
  by ring

/-
`sorry` is a placeholder that skips a proof for now without breaking the document flow.
**TO DO:** Replace `sorry` with the appropriate tactic below.
-/

example (a b c : ℝ) : (a + b) * c = a * c + b * c :=
  by sorry

example (a b c : ℝ) : (a + b) * (a + b) = a^2 + 2*a*b + b^2 :=
  by sorry

---

/-
## SECTION 4: REWRITING (rw)

/-
### THE REWRITE TACTIC (`rw`)
The `rw` tactic is your "Search and Replace" tool.
Whenever you have a named statement (a lemma, a hypothesis, or a definition) of the form `x = y`, `rw` finds `x` in your current goal and replaces it with `y`.

**Syntax Note:** `rw` must be followed by the name of the statement inside **square brackets**, e.g., `rw [h]`.
-/
-/

example (a b c : ℕ) : (strange_add a b) + c = 2*a + (b + c) := by
  rw [strange_add] -- Replaces the function name with its definition
  ring

-- **TO DO:** Use `rw` to prove the following.

example (a b c d x : ℝ) : horner_exp a b c d x = cubic_exp a b c d x := by
  sorry

--- Here, we proved a simple example of program equivalence, showing that two programs behave similarly on all possible inputs.

/-
## SECTION 5: FUNCTIONAL EXTENSIONALITY
Lean allows us to prove that two programs are equivalent. Don't worry too much about the specific tactics here; focus on the fact that we can prove two distinct programs behave identically on all inputs.
-/

example : horner_exp = cubic_exp := by
  funext a b c d x
  rw [horner_exp, cubic_exp]
  ring

def sq_diff (a b : ℝ) := (a + b)^2 - (a - b)^2
def alt_sq_diff (a b : ℝ) := 4 * (a * b)

-- **TO DO:** Prove the following. Don't forget you may need `rw`.
example (a b : ℝ) : sq_diff a b = alt_sq_diff a b := by
  sorry

---

/-
## SECTION 6: HYPOTHESES
`rw` can also invoke a hypothesis `h` provided in the lemma statement.
-/

example (a b : ℝ) (h : a = -b) : a + b = 0 := by
  rw [h]
  ring

-- **TO DO:** Prove this using the hypothesis `h`.
example (a b : ℝ) (h : b = 0) : a + b = a := by
  sorry

-- We can shorten multiple successive instances of rewrites, like in the following examples showing the same proof below:
example (a b c : ℝ) (h₁ : a = 3 * b) (h₂ : b = 2 * c) : a + b + c = 9 * c := by
  rw[h₁]
  rw[h₂]
  ring


example (a b c : ℝ) (h₁ : a = 3 * b) (h₂ : b = 2 * c) : a + b + c = 9 * c := by
  rw[h₁,h₂]
  ring

-- Using named lemmas:
lemma prod_sq (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 := by ring

example (a b : ℝ) (h : a^2 - b^2 > 0) : (a + b) * (a - b) > 0 := by
  rw [prod_sq]
  exact h -- `exact` means the goal matches the hypothesis 'h' perfectly.

---

/-
## SECTION 7: THE SIMPLIFIER (`simp`)

The `simp` tactic is Lean's "Auto-Cleaner." Its job is to reduce expressions to a **"Normal Form"** (the simplest possible version) by applying a battery of rules all at once.

### How it differs from `rw`:
1. **Automation:** `rw` is a surgical scalpel; it does one specific replacement. `simp` is more like a power-washer; it looks at the whole goal and cleans up everything it can.
2. **Library Knowledge:** `simp` automatically knows hundreds of standard library facts (like `x + 0 = x` or `x / x = 1`).

### `simp` vs. `simp [h]`:
* **`simp`**: Uses only the global "standard" rules.
* **`simp [h]`**: Sometimes, the proof requires a specific "local" fact (your`h` - which can be a local hypothesis, a definition, or a lemma) that isn't in the global library. By adding `[h]`, you are telling the simplifier: "Use all your normal rules, AND use this specific fact to help you."
-/

example (a b c : ℕ) (h : c > 0) : (a + b) + c*2 > (a + b) + 0 :=
  by simp [h]

/-
**TO DO:** (For Developers/Computer Scientists)
`as.length` returns list length. `as ++ bs` is list concatenation.
Can you prove this using `simp`?
-/

example (ls ms ks : List Nat) (h : ms.length = ks.length) : (ls ++ ms).length = (ls ++ ks).length :=
  by sorry

---

/-
## SECTION 8: CONGRUENCE (congr)
`congr` proves equalities by stripping away matching functions on both sides to reveal the arguments inside.
-/

example (a b : ℝ) (f : ℝ → ℝ) : f ((a + b)^2) = f (a^2 + 2*a*b + b^2) := by
  congr
  ring

-- `congr 1` limits how deep Lean looks.
example (a b : ℝ) (f : ℝ → ℝ) : f (a + b) = f (b + a) := by
  congr 1
  ring

-- **TO DO:** Solve using `congr`.
example (a b c d e : ℝ) (h : a + b = c) (g : d + e = c) (f : ℝ × ℝ → ℝ) : f (a + b, c) = f (c, d + e) := by
  sorry

---

/-
## SECTION 9: CALCULATIONS (calc)
`calc` allows you to chain a sequence of steps. Each line starts with `_` (representing the previous RHS). You can skip this section if time is short.
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by rw [h] -- Notice we can use tactics for each step
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring

-- **TO DO:** Fill in the tactics for this calculation.
example (a b c : ℝ) (h : a = -b) (h' : b + c = 0) : b*(a - c) = 0 := by
  calc
    b * (a - c) = b * a - b * c   := by ring
    _ = b * a + c * (-b)         := by ring
    _ = b * a + c * a           := by sorry
    _ = (b + c) * a             := by sorry
    _ = 0                       := by sorry

---

/-
## SECTION 10: INDUCTION
Induction handles goals involving Natural numbers by proving a base case (`zero`) and an inductive step (`succ`).
-/

example (n : ℕ) : 3 + n ≥ n := by
  induction n with
  | zero => simp
  | succ k ih => simp

-- **TO DO:** Prove using induction.
example (m n : ℕ) (h : m > 0) : m + n > n := by  sorry


/-
## SECTION 11: SUMMATION & PROGRAM PROPERTIES
We define a recursive function to compute the sum of the first `n` natural numbers.
-/


def sum_upto (n: Nat):=
  match n with
  | 0 => 0
  --This tells us that for n = 0, assign 0
  | n + 1 => (n + 1) + (sum_upto n)

#eval sum_upto 10

--the following lemma uses linarith, a powerful tactic, but you don't worry about that now. We will only use this lemma to prove the next example. For curiosity, you may learn to use this lemma post the tutorial.
lemma mul_dis (a b c : ℕ) : a * (b + 1 + c) = a * (b + 1) + a * c := by linarith


/-We will now use induction to prove that 2 times the sum of first n natural numbers, is equal to n*(n+1). We will above the standard formulation of this, since that might need us to adjust the types to account for division. -/

--We outlined the proof below, fill in the sorry
example (n : ℕ) : 2 * sum_upto n = n * (n + 1) := by
  induction n with
  | zero => simp [sum_upto]
  | succ k ih =>
    simp [sum_upto]
    simp[mul_dis]
    sorry



/- The above is an example of `proving program properties`. Not the most complicated example but worth an attempt. -/


/-`To Do:` define the factorial and prove that factorial of a number ≥ 3, is greater than the number. This is a bit consuming but worth an attempt.-/

/-For the last part, we leave you with an interesting outcome, a particular outcome of Lean's type system. We can define functions, which have proofs as inputs, and -/

def safe_div (m n : ℕ) (h : n ≠ 0) := m / n

--The function takes m n and a proof of n ≠ 0 as inputs, and outputs m/n. The output is thus only provided when it can be proved n ≠ 0. This kind of safe division, makes it extremely `type safe'.

#eval safe_div 3 2 (by simp)

--move the cursor to right after 2 above and and after simp to see what is happening.
