import Lax979537Proofs.StackCompare

namespace Lax762056Proofs.StackEqual

open Lax979537Proofs StackProgram StackTransfer StackCompare

variable {K Aux : Type} [DecidableEq K]

def equal (left right : K) : BitProgram K (Aux × Bool) :=
  .seq (scan left right)
    (.seq (.atom (.load (fun s => ((s.1.1, !(s.1.2 || s.2.isSome)), none))))
      (.seq (StackClear.clear left) (StackClear.clear right)))

theorem residue_equal (xs ys : List Bool) :
    (!((residue xs ys).leftPresent || (residue xs ys).rightHead.isSome)) =
      decide (xs.length = ys.length) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [residue]
  | cons b xs ih => cases ys <;> simp [residue, ih]

theorem clear_left (base : K → List Bool) (left right : K) (hne : left ≠ right)
    (xs ys : List Bool) (a : Aux × Bool) :
    Executes (StackClear.clear left) (working base left right xs ys a none)
      (working base left right [] ys a none) (2 * xs.length + 2) := by
  have h := StackClear.clear_store left (working base left right xs ys a none)
  have he : (⟨(a, none), Function.update (working base left right xs ys a none).stk left []⟩ :
      BitStore K (Aux × Bool)) = working base left right [] ys a none := by
    apply Store.ext
    · rfl
    · funext k
      by_cases hl : k = left
      · subst k; simp [working, hne]
      · by_cases hr : k = right
        · subst k; simp [working, hl]
        · simp [working, hl, hr]
  change Executes _ _ ⟨(a, none), Function.update (working base left right xs ys a none).stk left []⟩ _ at h
  rw [he] at h
  simpa [working, hne] using h

theorem clear_right (base : K → List Bool) (left right : K)
    (xs ys : List Bool) (a : Aux × Bool) :
    Executes (StackClear.clear right) (working base left right xs ys a none)
      (working base left right xs [] a none) (2 * ys.length + 2) := by
  simpa [working, Function.update_idem] using
    StackClear.clear_store right (working base left right xs ys a none)

theorem equal_executes (base : K → List Bool) (left right : K) (hne : left ≠ right)
    (xs ys : List Bool) (a : Aux) (flag : Bool) (scratch : Option Bool) :
    ∃ c, c ≤ 5 * (xs.length + ys.length) + 8 ∧
      Executes (equal left right) (working base left right xs ys (a, flag) scratch)
        (working base left right [] [] (a, decide (xs.length = ys.length)) none) c := by
  obtain ⟨c, hc, hh⟩ := scan_executes base left right hne xs ys a flag scratch
  have hl := Executes.atom
    (.load (fun s : (Aux × Bool) × Option Bool => ((s.1.1, !(s.1.2 || s.2.isSome)), none)))
    (working base left right (residue xs ys).left (residue xs ys).right
      (a, (residue xs ys).leftPresent) (residue xs ys).rightHead)
  change Executes _ _ (working base left right (residue xs ys).left (residue xs ys).right
    (a, !((residue xs ys).leftPresent || (residue xs ys).rightHead.isSome)) none) 1 at hl
  rw [residue_equal] at hl
  have h := Executes.seq hh (Executes.seq hl
    (Executes.seq (clear_left base left right hne (residue xs ys).left (residue xs ys).right _)
      (clear_right base left right [] (residue xs ys).right _)))
  refine ⟨_, ?_, h⟩
  have hs := residue_size xs ys
  omega

theorem equal_store (left right : K) (hne : left ≠ right) (s : BitStore K (Aux × Bool)) :
    ∃ c, c ≤ 5 * ((s.stk left).length + (s.stk right).length) + 8 ∧
      Executes (equal left right) s
        ⟨((s.state.1.1, decide ((s.stk left).length = (s.stk right).length)), none),
          Function.update (Function.update s.stk left []) right []⟩ c := by
  simpa only [working, Function.update_eq_self, Prod.mk.eta] using
    equal_executes s.stk left right hne (s.stk left) (s.stk right)
      s.state.1.1 s.state.1.2 s.state.2

end Lax762056Proofs.StackEqual
