import Mathlib.Tactic

/-!
# Lists and Algorithms

In the previous worksheet, we built `MyNat`, which was an infinite type.
Now, we define `MyList`, which is a chain of nodes that carry **data**.
-/

/-! ## 1. Defining the List -/

/-
We use `α` (alpha) to represent the type of data inside the list.

Note that **Lists** are different from **Natural Numbers** in the sense that...
-/

inductive MyList (α : Type) where
| empty : MyList α
| link  : α → MyList α → MyList α
deriving Repr, DecidableEq

namespace MyList

/-
**VISUALIZATION:**
Unlike MyNat, every 'link' node here holds a value 'a'.
`[1, 2, 3] = link 1 (link 2 (link 3 empty))`
`[4, 2]    = link 4 (link 2  empty))`
-/

def length {α} (l : MyList α) : Nat :=
match l with
| empty => 0
| link _ l' => 1 + (length l')
-- Note that the _ was wildcard defined earlier, since the length does not depend on the first element.

#check length
/-
To join two lists, we keep the first list's structure and replace its `empty` end
with the second list.
-/

def combine {α} (l : MyList α) (k : MyList α) : MyList α :=
match l with
| empty => k
| link c l' => link c (combine l' k)

infix: 51 "++" => combine

-- `Try`: What happens if you delete `{α}` above?

/-
**VISUALIZATION:**
We traverse the left list until the end, then hook it onto the right list.

We are combining `[2, 3] ++ [4, 5]`
-/

#eval (link (2:Nat) (link (3 :Nat) empty)) ++ (link (4:Nat) (link (5 :Nat) empty))

-- The following eval computes `[true] ++ [false, false]`

#eval (link (true) empty) ++ (link false (link false empty))

-- `Try`: What happens if we combine `(link (2:Nat) (link (3 :Nat) empty))` to `(link false (link false empty))`?
-- `Guess`: Why?


/-! ## 2. Writing Functional Code -/

def rev (l : MyList α) : MyList α :=
 match l with
 | empty => .empty
 | link c l' => (rev l') ++ (link c .empty)


def take (n : Nat) (l : MyList α):=
match l with
| empty => empty
| link hd tl => (link hd (take (n-1) tl))

#eval take 2 (link 3 (link 4 (link 5 empty : MyList Nat)))


/-
In the above functions, we use implicit types. It is not necessary that all the functions on lists
be defined on the broadest category of `lists over any given type (α)`.
Some of them can be defined for specific lists, for instance: list of Numbers, list of Strings,
list of Booleans et al.

Consider the function which takes a list of numbers and sums them up:
-/

def sum (l : MyList ℕ) : ℕ :=
 match l with
 | empty => 0
 | link hd tl => hd + sum tl


-- We define average of a list
def average (l : MyList ℕ) : ℚ :=
  sum l / (length l)

#eval average (link 2 (link 3 empty))

--`Question:` What is the average of an empty list? Why was the ℚ, the type of the co-domain of average?

-- We return to functions about lists

--`Question:` What does the following function do? Write a few eval's to check out incase you are in doubt.

def count_elem [BEq α] (l : MyList α) (el : α) : Nat :=
match l with
  | empty => 0
  | link hd tl =>
          (if (hd == el)
            then (1 + (count_elem tl el)) else (count_elem tl el))

--`Write a function occurs_in, which takes a list l and an element el and returns true only if the element el is in the list l. Fill in the sorry below.

def occurs_in [BEq α] (l : MyList α) (el : α) : Bool :=
 sorry

/-! ## 3. Higher Order Functions -/

/-
In this section, we introduce higher order functions. These are functions that can take
other functions as inputs. The `map` function below takes a function `f` as an input.
Since (nicely-behaved) functions translate to programs in functional programs, they can
be thought of as programs that can take other programs as inputs.

The following function **map** is supposed to take a function `f` and a list `l` and
return the list obtained by applying `f` to each element of the list.

Assume that `square : Nat → Nat` is a function that takes `n` and returns `n * n`,
`map (square) [3, 4, 5]` should return `[9, 16, 25]`.
-/

def map (f : α → β) (l : MyList α) : MyList β :=
match l with
| empty => empty
| link hd tl => (map f tl) -- Correct this.

/-
One simple 'test' to check whether your implementation is true is to see if the behaviour
is as expected on the given inputs. This is a testing based approach, not the strongest guarantees.
But at this point, we will use it to check if map is correct.
Ensure that given your map function, the following evaluations return true.
-/

#eval map (fun x => (x * 2)) (link 3 ( link 5 empty)) = link 6 (link 10 empty)

#eval map (fun x => (x == 2)) (link 3 ( link 5 empty)) = link true (link false empty)


/-
`filter` is another example of a higher-order function which is supposed to a take a predicate `P`
(a function from the type to Bool) and a list `l`, and return the list of all elements in `l`
which satisfy `P` (i.e., list of all elements in `l` for which `P x` is true).

Implementation here has a mistake, can you correct it?
-/

def filter (f : α → Bool) (l : MyList α) : MyList α :=
match l with
| empty => empty
| link hd tl => link hd tl

-- The filter function has to satisfy certain properties.

#eval filter (fun x => x == 0) (link 2 (link (-3) empty)) == empty

#eval filter (fun x => x == 0) (link 2 (link (-3) empty)) == empty

/-! ## 4. Proving Program Properties -/

/-
Before we proceed to more intense programs, let us prove some simple properties of programs.

We begin by proving that that length of two appended lists is the sum of the length of the lists.
-/

lemma length_combine (l k : MyList α) : length (l ++ k)  = length l + length k :=
by induction l with
| empty => simp [combine, length]
| link hd tl ih =>
   simp [combine]
   simp [length]
   simp [ih]
   linarith

lemma rev_preserves_len (l : MyList α) : length (rev l) = length l :=
by induction l with
| empty => rfl
| link hd tl ih =>
    simp [rev, length_combine, ih, length]
    sorry

lemma map_preserves_length (f : α → β) (l : MyList α) : length (map f l) = length l :=
by induction l with
| empty => sorry -- Correct It
| link hd tl ih => -- Correct It
    sorry

lemma filter_leq_length (P : α → Bool) (l : MyList α) : length (filter P l) ≤ length l :=
by induction l with
| empty => sorry -- Correct It
| link hd tl ih =>
  cases (P hd) with
  | true => sorry
  | false => sorry
-- Fill in the sorry's


/-! ## 5. Proving Equivalence of Programs -/

/-
The `rev` function defined earlier is *structurally simple* but *computationally slow*.
To see why, observe what happens when reversing a two-element list:

    rev (link 3 (link 4 empty))
  →  (rev (link 4 empty)) ++ (link 3 empty)
  → (rev empty ++ link 4 empty) ++ (link 3 empty)
  →  (empty ++ (link 4 empty)) ++ (link 3 empty)
  → (link 4 empty) ++ (link 3 empty)
  → link 4 (empty ++ (link 3 empty))
  → link 4 (link 3 empty)

The key issue is that `rev` repeatedly calls `combine`, which traverses a list
every time it is called.
Thus `rev` takes *quadratic* time in the length of the list.

We can eliminate this repeated traversal by using an *accumulator*.
The idea is:

  - As we walk down the list, we build up the reversed list in an extra argument.
  - Each step takes constant time.
  - When the input list is exhausted, the accumulator already *is* the final answer.

The helper function `fastrev_helper` implements this:

    fastrev_helper [3, 4] [] =
      fastrev_helper [4] (link 3 [])
    = fastrev_helper [] (link 4 (link 3 []))
    = link 4 (link 3 [])

Notice how the list is reversed *on the fly*, without any calls to `combine`.

Thus, `fastrev` runs in linear time:
`fastrev l = fastrev_helper l empty`
-/

def fastrev_helper (l : MyList α) (k : MyList α) : MyList α :=
  match l with
  | empty => k
  | link hd tl => fastrev_helper tl (link hd k)

def fastrev (l : MyList α) : MyList α :=
  fastrev_helper l empty

/-
Our aim now is to prove that `rev` and `fastrev` are equivalent.
It is not obvious straightaway, but the proof breaks cleanly into the following 4 steps:

1. **Prove basic facts about `combine`.**
   Show that `combine` has `empty` as a right identity:
        `combine l empty = l`
   and that it is associative:
        `combine l (combine k m) = combine (combine l k) m`

2. **Prove the key accumulator lemma.**
   Show that `fastrev_helper` behaves exactly like `rev` followed by `combine`:
        `fastrev_helper l k = combine (rev l) k`
   This is proved by induction on `l`.
   In the inductive step, you will need the associativity of `combine` from Step 1.

3. **Specialise the accumulator to `empty`.**
   By substituting `k = empty` into the lemma of Step 2, you obtain:
        `fastrev_helper l empty = combine (rev l) empty`

4. **Use the right identity of `combine` to conclude.**
   Since `combine l empty = l`, the above becomes:
        `fastrev_helper l empty = rev l`
   and because `fastrev l` is *defined* as `fastrev_helper l empty`,
   we finally obtain:
        `fastrev l = rev l`

These four steps together give a clean and structured proof that the
tail-recursive version of reverse is extensionally equal to the naïve one.
-/

-- **Step 1 : Algebra of Combine**

lemma combine_empty_right (l : MyList α) :
  l ++ empty = l := by
  sorry -- write an induction proof of this

lemma combine_assoc (l k m : MyList α) :
  l ++ (k ++ m) = (l ++ k) ++ m := by
  induction l with
  | empty =>
      simp [combine]
  | link h t ih =>
      simp [combine]
      sorry

-- **Step 2: How combine interacts with rev**

lemma rev_combine (l k : MyList α) :
  rev (l ++ k) = (rev k) ++ (rev l) := by
  induction l with
  | empty =>
      simp [combine, rev, combine_empty_right]
  | link h t ih =>
      simp [combine, rev]
      -- You will now need associativity of combine,
      -- and the IH.
      sorry

-- **Step 3: fastrev_helper and rev equivalence**

lemma fastrev_helper_rev_combine (l k : MyList Nat) :
  fastrev_helper l k = (rev l) ++ k := by
  induction l generalizing k with
  | empty =>
      simp [fastrev_helper, rev, combine]
  | link hd tl ih =>
      -- Inductive case. We show the structure of the calculation.
      calc
        fastrev_helper (link hd tl) k
            = fastrev_helper tl (link hd k) := by
                simp [fastrev_helper]
        _   = (rev tl) ++ (link hd k) := by
                -- note that ih cannot be directly applied here, it needs to be instantiated
                -- for a particular term to be applied
                rw [ih (link hd k)]
        _   = (rev (link hd tl)) ++ k := by sorry

-- **Step 4: Proving the final lemma**

--Hint: You don't need induction for the following lemma.
lemma rev_fastrev_eq : ∀(l : MyList α), rev l = fastrev l := by
  sorry



/-
## 4. Two Ways to Define Sortedness


## How do we check if a list is sorted?
We give two approaches.


### ### Approach A: Boolean Check
A function that traverses a list and returns `true` if it is sorted
and `false` otherwise.
-/


def isSortedBool (l : MyList Nat) : Bool :=
match l with
| empty => true
| link _ empty => true
| link x (link y l') => x ≤ y ∧ isSortedBool (link y l')


/-!
### Approach B: Inductive Predicate
A logical definition describing *why* a list is sorted.
1. Empty list is sorted.
2. Singleton list is sorted.
3. If `x ≤ y` and `(y :: xs)` is sorted, then `x :: y :: xs` is sorted.
-/


inductive Sorted : MyList Nat → Prop where
| nil : Sorted MyList.empty
| singleton : ∀ x, Sorted (MyList.link x MyList.empty)
| cons : ∀ {x y xs}, x ≤ y → Sorted (link y xs) → Sorted (link x (link y xs))





-- # Insertion Sort Definitions

/-!
## Insertion Sort
We define the classic insertion sort algorithm:
1. `insertSorted`: Insert a new element into a sorted list.
2. `insertionSort`: Recursively sort the tail and insert the head.
-/

/-!
## Insertion Sort
We define the classic insertion sort algorithm:
1. `insertSorted`: Insert a new element into a sorted list.
2. `insertionSort`: Recursively sort the tail and insert the head.
-/


def insertSorted (x : Nat) (l : MyList Nat) : MyList Nat :=
match l with
| empty => link x empty
| link y l' =>
if x ≤ y then link x (link y l')
else link y (insertSorted x l')


def insertionSort (l : MyList Nat) : MyList Nat :=
match l with
| empty => empty
| link x l' => insertSorted x (insertionSort l')


-- VISUALIZATION EXPLANATION:
-- The element `x` recursively "bubbles down" until it finds
-- its correct position inside the partially sorted list.




-- ############################################################
-- # Lemmas
-- ############################################################


/-!
A short lemma: If `(x :: xs)` is sorted, then `xs` is sorted.
-/

lemma sorted_of_cons (x : Nat) (xs : MyList Nat)
(h : Sorted (link x xs)) : Sorted xs := by
cases h with
| singleton => apply Sorted.nil
| cons _ htail => exact htail


/-!
Insertion sort preserves length.
(This is needed for future correctness proofs.)
-/


/-!
Inserting an element into a sorted list keeps it sorted. `Fill in the sorry here`. Carefully observe what each step is doing.
-/

lemma insert_preserves_sorted (l : MyList Nat) (x : Nat)
(h : Sorted l) : Sorted (insertSorted x l) := by
induction l generalizing x with
| empty => simp [insertSorted, Sorted.singleton]
| link y ys ih =>
  cases h with
  | singleton =>
    by_cases hx : x ≤ y
    simp [insertSorted, hx]
    apply Sorted.cons hx (Sorted.singleton y)
    simp [insertSorted, hx]
    --linarith uses the inbuilt linear arithmetic solver
    apply Sorted.cons (by linarith [hx]) (Sorted.singleton x)
  | cons hy1 hy2 =>
    rename_i y' ys'
    --rename_i gives provides to variables, go above and see what it is doing.
    by_cases hx : x ≤ y
    simp [insertSorted, hx]
    have h_sorted_rest : Sorted (link y (link y' ys')) := by
      have h_insert_y : Sorted (insertSorted y (link y' ys')) := ih y hy2
      simp [insertSorted, hy1] at h_insert_y
      exact h_insert_y
    apply (Sorted.cons hx h_sorted_rest)
    have hy_lt_x : y < x := by linarith[hx]
    have h_eq : insertSorted x (link y (link y' ys')) = link y (insertSorted x (link y' ys')) := by
      simp [insertSorted]
      exact fun w => False.elim (hx w)
    have hy_le_x : y ≤ x := Nat.le_of_not_ge hx
    have sorted_tail : Sorted (insertSorted x (link y' ys')) := ih x hy2
    sorry -- Finish the proof.

lemma insertS_is_sorted (l: MyList Nat) : Sorted (insertionSort l) := by sorry

/-!
Main theorem: insertion sort produces a sorted list. Can you speculate, what are the other properties to prove its correctness?
-/
