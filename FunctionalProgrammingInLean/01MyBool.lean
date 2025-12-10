import Mathlib
--=================================================================
-- WORKSHEET: Functional Programming and Logic in Lean 4
-- =================================================================

-- We first create a simple type consisting of finitely many objects.
-- The simplest object in this paradigm is Bool. Since Bool already
-- exists as a standard type, we will create our own called MyBool.
-- By convention: 'sashem' acts like True, 'khorem' acts like False.

inductive MyBool where
| sashem : MyBool  -- behaves like "true"
| khorem : MyBool  -- behaves like "false"
deriving Repr, DecidableEq

-- -----------------------------------------------------------------
-- 1. Basic Definitions and Pattern Matching
-- -----------------------------------------------------------------

-- We define a function by allotting a value to each case.
def negate (p : MyBool) : MyBool :=
  match p with
  | .sashem => .khorem
  | .khorem => .sashem

-- EVALUATION CHECKS
#eval negate .sashem            -- expect: khorem
#eval negate .khorem            -- expect: sashem
#eval negate (negate .sashem)   -- expect: sashem

-- NOTE on Namespaces:
-- In the functions above, we explicitly put a `.` before sashem.
-- This is shorthand for `MyBool.sashem`. To avoid typing this repeatedly,
-- we can open the namespace.

open MyBool

-- Now we can refer to `sashem` and `khorem` directly.

#eval negate sashem
#eval negate khorem

-- -----------------------------------------------------------------
-- 2. Logical Operators (AND / OR)
-- -----------------------------------------------------------------

-- A naive definition of AND listing all 4 combinations:
def naive_my_and (p : MyBool) (q : MyBool) : MyBool :=
  match p, q with
  | sashem, sashem => sashem
  | sashem, khorem => khorem
  | khorem, sashem => khorem
  | khorem, khorem => khorem

#eval naive_my_and sashem khorem
#eval naive_my_and sashem (naive_my_and sashem sashem)

-- OPTIMIZATION: Using Wildcards (_)
-- We can simplify this. `my_and` is only true if both inputs are true.
-- For all other cases, it is false.

def shorter_my_and (p : MyBool) (q : MyBool) : MyBool :=
  match p, q with
  | sashem, sashem => sashem
  | _, _ => khorem

-- The `_` is a wildcard that matches "anything else".

-- Even shorter: Pattern match only on `p`.
-- If p is true, the result depends entirely on q.
-- If p is false, the result is always false.
def my_and (p : MyBool) (q : MyBool) : MyBool :=
  match p with
  | sashem => q
  | _ => khorem

-- DEFINING OR
-- logic: returns true (sashem) if at least one input is true.
def my_or (p : MyBool) (q : MyBool): MyBool :=
  match p with
  | sashem => sashem -- If p is true, result is true immediately
  | _ => q           -- If p is false, result depends on q

-- INFIX NOTATION
-- We can assign symbols to these functions.
infix:50 " + " => my_or
infix:51 " * " => my_and   -- Changed from x to * for standard typing

#eval sashem + khorem
#eval khorem * sashem

-- -----------------------------------------------------------------
-- 3. Implication (The Logic Task)
-- -----------------------------------------------------------------

-- TASK: Write a function my_implies.
-- Mathematical Rule: p → q is FALSE only when p is True and q is False.
-- In all other cases, it is TRUE.

def my_implies (p : MyBool) (q : MyBool) : MyBool :=
  match p with
  | sashem => q
  -- If p is true, we must check q
  | khorem => sashem
  -- If p is false, implication is logically true

-- We prove that negating twice returns the original value.

example (p : MyBool) : negate (negate p) = p := by
  cases p with
  | sashem => simp [negate]
  | khorem => simp [negate]

-- De Morgan's Law: ¬(p ∧ q) = ¬p ∨ ¬q

example (p : MyBool) (q : MyBool) :
  negate (my_and p q) = my_or (negate p) (negate q) := by
    cases p with
    | sashem => simp [negate, my_and, my_or]
    | khorem => simp [negate, my_and, my_or]

--Since the proofs in both the cases are similar, we can instead write it in a short way as following:
example (p : MyBool) (q : MyBool) :
  negate (my_and p q) = my_or (negate p) (negate q) := by
    cases p <;> simp [negate, my_and, my_or]
--The above applies the provided to both the goals created by cases.

-- `TASK`: Prove De Morgan's Law for OR: ¬(p ∨ q) = ¬p ∧ ¬q
example (p : MyBool) (q : MyBool) :
  negate (my_or p q) = my_and (negate p) (negate q) := by
  cases p <;> simp [negate, my_or, my_and]

-- `TASK`: State and prove that p → q is equal to ¬p ∨ q
example (p q : MyBool) :
  my_implies p q = my_or (negate p) q := sorry

example (p q : MyBool) :
 naive_my_and p q =  my_and p q
 := by cases p <;> cases q <;> simp [naive_my_and, my_and]
 --note that naive_my_and does pattern matching over p and q, so we need to consider the cases associated with q as well. We do so in the fashion above.

/- above is a simple example of showing two 'programs' (functions that compute) exhibit the same behaviour. This is an important problem in formal methods, where the idea is to show whether an optimized code is equivalent to a non optimized code-/
-- -----------------------------------------------------------------
-- 5. Mapping to Natural Numbers
-- -----------------------------------------------------------------

def boolean_number (p : MyBool) : Nat :=
  match p with
  | sashem => 1
  | khorem => 0

--prove the following:
example (p : MyBool) (q : MyBool) :
  boolean_number (my_or p q) = max (boolean_number p) (boolean_number q) := sorry

-- TASK: Prove AND corresponds to multiplication

example (p : MyBool) (q : MyBool):
  boolean_number (my_and p q) = (boolean_number p) * (boolean_number q) := by sorry

-- -----------------------------------------------------------------
-- 6. Currying
-- -----------------------------------------------------------------

-- In Lean, `MyBool → MyBool → MyBool` means `MyBool → (MyBool → MyBool)`.
-- A function takes one argument and returns a NEW function.

def and_sashem := my_and sashem
-- `and_sashem` is now a function waiting for the second argument.

example: ∃ q, and_sashem q = sashem := by
  use sashem
  rfl -- rfl proves equality by simple calculation

def and_khorem := my_and khorem

lemma all_q : ∀ q, and_khorem q = khorem := by
  intro q
  simp [and_khorem, my_and]

-- -----------------------------------------------------------------
-- 7. Higher-Order Functions
-- -----------------------------------------------------------------

def apply_fn (f : MyBool → MyBool) (p : MyBool) (q : MyBool) : MyBool :=
  my_or (f p) (f q)

#eval apply_fn negate sashem khorem

-- -----------------------------------------------------------------
-- 8. Inductive Types: Traffic Lights
-- -----------------------------------------------------------------

inductive TrafficLight where
| Red
| Yellow
| Green
deriving Repr, DecidableEq

namespace TrafficLight

def next (t : TrafficLight) : TrafficLight :=
  match t with
  | Red => Yellow
  | Yellow => Green
  | Green => Red

-- TASK: Prove that a light never changes to itself.
-- Hint: We need `intro` to bring `t` into the context,
-- then `cases t` to check every color.
example : ∀ t, next t ≠ t := by
  sorry


end TrafficLight

-- FUN EXERCISE:
-- Define Z4 (integers modulo 4) as a type with 4 constructors:
-- Zero, One, Two, Three.
-- Define an addition function `add_z4`.
-- Example test: #eval add_z4 Two Three -- should equal One
