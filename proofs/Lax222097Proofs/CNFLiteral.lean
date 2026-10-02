import Lax222097Proofs.CNFPrefix
import Lax222097Proofs.QueryCompiler.StackUnary
import Lax222097Proofs.QueryCompiler.StackClear

namespace Lax222097Proofs.CNFLiteral

open Lax222097Proofs.QueryCompiler StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def readLiteral (src index : K) : BitProgram K (Aux × Bool) :=
  .seq (StackUnary.parse src index)
    (.atom (.pop src (fun s b => ((s.1.1, b.getD false), none))))

theorem splitUnary (n : ℕ) (tail : List Bool) :
    StackUnary.splitUnary (List.replicate n true ++ false :: tail) = (n, some tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, StackUnary.splitUnary, ih]

theorem readLiteral_executes (base : K → List Bool) (src index : K) (hne : src ≠ index)
    (l : ShortCNF.Literal) (tail : List Bool) (a : Aux) (old : Bool) (b : Option Bool) :
    Executes (readLiteral src index)
      (working base src index (ShortCNF.encodeLiteral l ++ tail) [] (a, old) b)
      (working base src index tail (List.replicate l.1 true) (a, l.2) none) (3 * l.1 + 3) := by
  have hp := StackUnary.parse_executes base src index hne
    (List.replicate l.1 true ++ false :: l.2 :: tail) [] (a, old) b
  rw [splitUnary] at hp
  simp only [Option.getD_some, List.append_nil, StackUnary.finished, Option.map_some] at hp
  have hr := Executes.atom
    (.pop src (fun s : (Aux × Bool) × Option Bool => fun b => ((s.1.1, b.getD false), none)))
    (working base src index (l.2 :: tail) (List.replicate l.1 true) (a, old) (some false))
  have he : Op.apply
      (.pop src (fun s : (Aux × Bool) × Option Bool => fun b => ((s.1.1, b.getD false), none)))
      (working base src index (l.2 :: tail) (List.replicate l.1 true) (a, old) (some false)) =
      working base src index tail (List.replicate l.1 true) (a, l.2) none := by
    apply Store.ext
    · simp [Op.apply, working, hne]
    · funext k
      by_cases hs : k = src <;> by_cases hi : k = index <;> simp_all [Op.apply, working]
  rw [he] at hr
  simpa [readLiteral, ShortCNF.encodeLiteral, List.append_assoc, Nat.add_assoc] using Executes.seq hp hr

def readAt (src index : K) : ℕ → BitProgram K (Aux × Bool)
  | 0 => .seq (read src) (.branch (fun s => s.2 == some true)
      (.seq (StackClear.clear index) (.seq (readLiteral src index) CNFScan.reset)) CNFScan.reset)
  | k + 1 => .seq (read src) (.branch (fun s => s.2 == some true)
      (.seq (StackClear.clear index) (.seq (readLiteral src index) (readAt src index k))) CNFScan.reset)

def chosen : ℕ → ShortCNF.Clause → ShortCNF.Literal → ShortCNF.Literal
  | _, [], old => old
  | 0, l :: _, _ => l
  | k + 1, l :: C, _ => chosen k C l

def rest : ℕ → ShortCNF.Clause → List Bool → List Bool
  | _, [], tail => tail
  | 0, _ :: C, tail => ShortCNF.encodeClause C ++ tail
  | k + 1, _ :: C, tail => rest k C tail

def time : ℕ → ShortCNF.Clause → ShortCNF.Literal → ℕ
  | _, [], _ => 3
  | 0, l :: _, old => 2 * old.1 + 3 * l.1 + 8
  | k + 1, l :: C, old => 2 * old.1 + 3 * l.1 + 7 + time k C l

theorem clear_index (base : K → List Bool) (src index : K) (xs ys : List Bool)
    (a : Aux) (old : Bool) (b : Option Bool) :
    Executes (StackClear.clear index) (working base src index xs ys (a, old) b)
      (working base src index xs [] (a, old) none) (2 * ys.length + 2) := by
  simpa [working, Function.update_idem] using
    StackClear.clear_store index (working base src index xs ys (a, old) b)

theorem reset_working (base : K → List Bool) (src index : K) (xs ys : List Bool)
    (a : Aux) (old : Bool) (b : Option Bool) :
    Executes (CNFScan.reset : BitProgram K (Aux × Bool)) (working base src index xs ys (a, old) b)
      (working base src index xs ys (a, old) none) 1 := Executes.atom _ _

theorem read_src (base : K → List Bool) (src index : K) (hne : src ≠ index) (xs ys : List Bool)
    (a : Aux) (old : Bool) (b : Option Bool) :
    Executes (read src) (working base src index xs ys (a, old) b)
      (working base src index xs.tail ys (a, old) xs.head?) 1 := by
  have h := Executes.atom (.pop src (fun s : (Aux × Bool) × Option Bool => fun b => (s.1, b)))
    (working base src index xs ys (a, old) b)
  rw [pop_working base src index hne] at h
  exact h

/-- Read one of the first three literals, repeating the last available
literal when a short clause needs padding. Work on arbitrary indices too. -/
theorem readAt_executes (base : K → List Bool) (src index : K) (hne : src ≠ index)
    (k : ℕ) (C : ShortCNF.Clause) (tail : List Bool) (a : Aux)
    (old : ShortCNF.Literal) (b : Option Bool) :
    Executes (readAt src index k)
      (working base src index (ShortCNF.encodeClause C ++ tail) (List.replicate old.1 true) (a, old.2) b)
      (working base src index (rest k C tail) (List.replicate (chosen k C old).1 true)
        (a, (chosen k C old).2) none) (time k C old) := by
  induction k generalizing C old b with
  | zero =>
    cases C with
    | nil =>
      exact Executes.seq (read_src base src index hne (false :: tail) _ a old.2 b)
        (Executes.branch_false rfl (reset_working base src index tail _ a old.2 (some false)))
    | cons l C =>
      have hs := read_src base src index hne
        (true :: (ShortCNF.encodeLiteral l ++ (ShortCNF.encodeClause C ++ tail))) (List.replicate old.1 true) a old.2 b
      have hc := clear_index base src index (ShortCNF.encodeLiteral l ++ (ShortCNF.encodeClause C ++ tail))
        (List.replicate old.1 true) a old.2 (some true)
      have hl := readLiteral_executes base src index hne l (ShortCNF.encodeClause C ++ tail) a old.2 none
      have hr := reset_working base src index (ShortCNF.encodeClause C ++ tail)
        (List.replicate l.1 true) a l.2 none
      have h := Executes.seq hs (Executes.branch_true (q := CNFScan.reset)
        (b := fun s : (Aux × Bool) × Option Bool => s.2 == some true) rfl
        (Executes.seq hc (Executes.seq hl hr)))
      convert h using 1 <;>
        simp [readAt, rest, chosen, time, ShortCNF.encodeClause, ShortCNF.encodeList, List.append_assoc] <;> omega
  | succ k ih =>
    cases C with
    | nil =>
      exact Executes.seq (read_src base src index hne (false :: tail) _ a old.2 b)
        (Executes.branch_false rfl (reset_working base src index tail _ a old.2 (some false)))
    | cons l C =>
      have hs := read_src base src index hne
        (true :: (ShortCNF.encodeLiteral l ++ (ShortCNF.encodeClause C ++ tail))) (List.replicate old.1 true) a old.2 b
      have hc := clear_index base src index (ShortCNF.encodeLiteral l ++ (ShortCNF.encodeClause C ++ tail))
        (List.replicate old.1 true) a old.2 (some true)
      have hl := readLiteral_executes base src index hne l (ShortCNF.encodeClause C ++ tail) a old.2 none
      have h := Executes.seq hs (Executes.branch_true (q := CNFScan.reset)
        (b := fun s : (Aux × Bool) × Option Bool => s.2 == some true) rfl
        (Executes.seq hc (Executes.seq hl (ih C l none))))
      convert h using 1 <;>
        simp [readAt, rest, chosen, time, ShortCNF.encodeClause, ShortCNF.encodeList, List.append_assoc] <;> omega

theorem time_bound (k : ℕ) (C : ShortCNF.Clause) (old : ShortCNF.Literal) (L : ℕ)
    (hC : ∀ l ∈ C, l.1 ≤ L) (ho : old.1 ≤ L) : time k C old ≤ (k + 1) * (5 * L + 10) := by
  induction k generalizing C old with
  | zero =>
    cases C with
    | nil => simp [time]
    | cons l C => have := hC l (by simp); simp only [time]; omega
  | succ k ih =>
    cases C with
    | nil => simp only [time]; nlinarith
    | cons l C =>
      have hl := hC l (by simp)
      have hr := ih C l (fun v hv => hC v (by simp [hv])) hl
      simp only [time]
      nlinarith

end Lax222097Proofs.CNFLiteral
