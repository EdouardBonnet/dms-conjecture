import Lax979537Proofs.StackRepeat

namespace Lax762056Proofs.StackCount

open Lax979537Proofs StackProgram StackTransfer StackRepeat

variable {K Aux : Type} [DecidableEq K]

def push (dst : K) : BitProgram K Aux := .atom (.push dst (fun _ => true))
def pushed (dst : K) (s : BitStore K Aux) : BitStore K Aux := Op.apply (.push dst (fun _ => true)) s
def count (src dst : K) : BitProgram K Aux := repeatCount src (push dst)

theorem pushed_working (base : K → List Bool) (src dst : K) (xs ys : List Bool)
    (a : Aux) (b : Option Bool) :
    pushed dst (working base src dst xs ys a b) = working base src dst xs (true :: ys) a b := by
  simp [pushed, Op.apply, working, Function.update_idem]

theorem result_working (base : K → List Bool) (src dst : K) (hne : src ≠ dst)
    (xs ys : List Bool) (a : Aux) (b : Option Bool) :
    result src (pushed dst) xs.length (working base src dst xs ys a b) =
      working base src dst [] (List.replicate xs.length true ++ ys) a none := by
  induction xs generalizing ys b with
  | nil => simpa only [result, List.length_nil, List.replicate_zero, List.nil_append] using
      pop_working base src dst hne [] ys a b
  | cons x xs ih =>
    simp only [List.length_cons, result]
    rw [show readStore src (working base src dst (x :: xs) ys a b) =
      working base src dst xs ys a (some x) from pop_working base src dst hne (x :: xs) ys a b]
    rw [pushed_working, ih]
    simp [List.replicate_succ', List.append_assoc]

/-- Consume any binary word and put its length in a unary stack. -/
theorem count_executes (base : K → List Bool) (src dst : K) (hne : src ≠ dst)
    (xs ys : List Bool) (a : Aux) (b : Option Bool) :
    ∃ c, c ≤ 3 * xs.length + 2 ∧
      Executes (count src dst) (working base src dst xs ys a b)
        (working base src dst [] (List.replicate xs.length true ++ ys) a none) c := by
  have h := repeat_executes src (push dst) (pushed dst) (fun _ => True) 1
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun s _ => by simp [pushed, Op.apply, hne])
    (fun s _ => ⟨1, le_refl _, Executes.atom _ _⟩) (working base src dst xs ys a b) trivial
  have he : (working base src dst xs ys a b).stk src = xs := by simp [working, hne]
  rw [he, result_working base src dst hne] at h
  exact h

end Lax762056Proofs.StackCount
