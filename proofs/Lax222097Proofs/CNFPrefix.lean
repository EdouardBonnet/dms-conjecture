import Lax222097Proofs.CNFScan

namespace Lax222097Proofs.CNFPrefix

open Lax222097Proofs.QueryCompiler StackProgram StackTransfer StackRepeat CNFScan

variable {K Aux : Type} [DecidableEq K]

def contents : Option ShortCNF.Formula → List Bool
  | none => []
  | some F => ShortCNF.encode F

def next : Option ShortCNF.Formula → Option ShortCNF.Formula
  | none | some [] => none
  | some (_ :: F) => some F

def after : ℕ → Option ShortCNF.Formula → Option ShortCNF.Formula
  | 0, F => F
  | n + 1, F => after n (next F)

theorem next_length (F : Option ShortCNF.Formula) : (contents (next F)).length ≤ (contents F).length := by
  rcases F with _ | F
  · rfl
  cases F <;> simp [next, contents, ShortCNF.encode, ShortCNF.encodeList]
  omega

def skipNext (src : K) : BitProgram K Aux :=
  .seq (read src) (.branch (fun s => s.2 == some true) (skipClause src) reset)

theorem skipNext_executes (base : K → List Bool) (src : K) (F : Option ShortCNF.Formula)
    (a : Aux) (b : Option Bool) :
    ∃ c, c ≤ 2 * (contents F).length + 3 ∧
      Executes (skipNext src) (store base src (contents F) a b)
        (store base src (contents (next F)) a none) c := by
  rcases F with _ | F
  · exact ⟨3, by simp [contents],
      Executes.seq (read_store base src [] a b)
        (Executes.branch_false rfl (reset_executes base src [] a none))⟩
  cases F with
  | nil =>
    exact ⟨3, by simp [contents, ShortCNF.encode, ShortCNF.encodeList],
      Executes.seq (read_store base src [false] a b)
        (Executes.branch_false rfl (reset_executes base src [] a (some false)))⟩
  | cons C F =>
    have hc := skipClause_linear base src C (ShortCNF.encode F) a (some true)
    have h := Executes.seq
      (read_store base src (true :: (ShortCNF.encodeClause C ++ ShortCNF.encode F)) a b)
      (Executes.branch_true (q := reset) (b := fun s : Aux × Option Bool => s.2 == some true) rfl hc)
    refine ⟨1 + ((2 * (ShortCNF.encodeClause C).length + 1) + 1), ?_, h⟩
    simp [contents, ShortCNF.encode, ShortCNF.encodeList]
    omega

theorem prefixLoop_executes (base : K → List Bool) (counter src : K) (hne : counter ≠ src)
    (n L : ℕ) (F : Option ShortCNF.Formula) (hL : (contents F).length ≤ L) (a : Aux) :
    ∃ c, c ≤ (2 * L + 5) * n + 1 ∧
      Executes (repeatLoop counter (skipNext src))
        (working base counter src (List.replicate n true).tail (contents F) a
          (List.replicate n true).head?)
        (working base counter src [] (contents (after n F)) a none) c := by
  induction n generalizing F with
  | zero => exact ⟨1, by omega, Executes.loop_false rfl⟩
  | succ n ih =>
    obtain ⟨c, hc, hs⟩ := skipNext_executes (Function.update base counter (List.replicate n true))
      src F a (some true)
    obtain ⟨d, hd, ht⟩ := ih (next F) ((next_length F).trans hL)
    have hr := Executes.atom (.pop counter (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (working base counter src (List.replicate n true) (contents (next F)) a none)
    rw [pop_working base counter src hne] at hr
    have h := Executes.loop_true (p := .seq (skipNext src) (read counter))
      (b := fun s : Aux × Option Bool => s.2.isSome) rfl (Executes.seq hs hr) ht
    refine ⟨(c + 1) + d + 1, ?_, ?_⟩
    · simp only [Nat.mul_succ]
      omega
    · simpa [repeatLoop, after, List.replicate_succ] using! h

/-- Skip a requested number of clauses. Requests past the last clause are
defined and still satisfy the same quadratic bound. -/
theorem prefix_executes (base : K → List Bool) (counter src : K) (hne : counter ≠ src)
    (n L : ℕ) (F : Option ShortCNF.Formula) (hL : (contents F).length ≤ L)
    (a : Aux) (b : Option Bool) :
    ∃ c, c ≤ (2 * L + 5) * n + 2 ∧
      Executes (repeatCount counter (skipNext src))
        (working base counter src (List.replicate n true) (contents F) a b)
        (working base counter src [] (contents (after n F)) a none) c := by
  obtain ⟨c, hc, h⟩ := prefixLoop_executes base counter src hne n L F hL a
  have hr := Executes.atom (.pop counter (fun s : Aux × Option Bool => fun b => (s.1, b)))
    (working base counter src (List.replicate n true) (contents F) a b)
  rw [pop_working base counter src hne] at hr
  exact ⟨1 + c, by omega, Executes.seq hr h⟩

theorem after_some (F : ShortCNF.Formula) (n : ℕ) (h : n ≤ F.length) :
    after n (some F) = some (F.drop n) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    cases F with
    | nil => simp at h
    | cons C F =>
      simpa [after, next] using ih F (by simpa using h)

theorem after_none (n : ℕ) : after n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem after_past (F : ShortCNF.Formula) (n : ℕ) (h : F.length < n) :
    after n (some F) = none := by
  induction n generalizing F with
  | zero => omega
  | succ n ih =>
    cases F with
    | nil => exact after_none n
    | cons C F => exact ih F (by simpa using h)

end Lax222097Proofs.CNFPrefix
