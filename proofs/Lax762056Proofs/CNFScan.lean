import Lax762056Proofs.ShortCNF
import Lax762056Proofs.QueryCompiler.StackRepeat

set_option backward.isDefEq.respectTransparency false

namespace Lax762056Proofs.CNFScan

open Lax762056Proofs.QueryCompiler StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def store (base : K → List Bool) (src : K) (xs : List Bool) (a : Aux) (b : Option Bool) :
    BitStore K Aux := ⟨(a, b), Function.update base src xs⟩

theorem read_store (base : K → List Bool) (src : K) (xs : List Bool)
    (a : Aux) (b : Option Bool) :
    Executes (read src) (store base src xs a b) (store base src xs.tail a xs.head?) 1 := by
  have h := Executes.atom (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
    (store base src xs a b)
  simpa [StackTransfer.read, store, Op.apply, Function.update_idem] using h

def unaryLoop (src : K) : BitProgram K Aux := .loop (fun s => s.2 == some true) (read src)
def skipUnary (src : K) : BitProgram K Aux := .seq (read src) (unaryLoop src)
def reset : BitProgram K Aux := .atom (.load (fun s => (s.1, none)))

theorem unaryLoop_executes (base : K → List Bool) (src : K) (n : ℕ) (tail : List Bool)
    (a : Aux) :
    Executes (unaryLoop src)
      (store base src (List.replicate n true ++ false :: tail).tail a
        (List.replicate n true ++ false :: tail).head?)
      (store base src tail a (some false)) (2 * n + 1) := by
  induction n with
  | zero => exact Executes.loop_false rfl
  | succ n ih =>
    have h := Executes.loop_true (p := read src) (b := fun s : Aux × Option Bool => s.2 == some true)
      (s := store base src (List.replicate n true ++ false :: tail) a (some true)) rfl
      (read_store base src _ a (some true)) ih
    convert! h using 1 <;> simp [unaryLoop, List.replicate_succ] <;> omega

theorem skipUnary_executes (base : K → List Bool) (src : K) (n : ℕ) (tail : List Bool)
    (a : Aux) (b : Option Bool) :
    Executes (skipUnary src) (store base src (List.replicate n true ++ false :: tail) a b)
      (store base src tail a (some false)) (2 * n + 2) := by
  have h := Executes.seq (read_store base src _ a b) (unaryLoop_executes base src n tail a)
  convert! h using 1 <;> omega

theorem reset_executes (base : K → List Bool) (src : K) (xs : List Bool)
    (a : Aux) (b : Option Bool) :
    Executes (reset : BitProgram K Aux) (store base src xs a b) (store base src xs a none) 1 :=
  Executes.atom _ _

def skipLiteral (src : K) : BitProgram K Aux :=
  .seq (skipUnary src) (.seq (read src) reset)

theorem skipLiteral_executes (base : K → List Bool) (src : K) (l : ShortCNF.Literal)
    (tail : List Bool) (a : Aux) (b : Option Bool) :
    Executes (skipLiteral src) (store base src (ShortCNF.encodeLiteral l ++ tail) a b)
      (store base src tail a none) (2 * l.1 + 4) := by
  have h := Executes.seq (skipUnary_executes base src l.1 (l.2 :: tail) a b)
    (Executes.seq (read_store base src (l.2 :: tail) a (some false))
      (reset_executes base src tail a (some l.2)))
  simpa [skipLiteral, ShortCNF.encodeLiteral, List.append_assoc, Nat.add_assoc] using h

def clauseLoop (src : K) : BitProgram K Aux :=
  .loop (fun s => s.2 == some true) (.seq (skipLiteral src) (read src))

def skipClause (src : K) : BitProgram K Aux :=
  .seq (read src) (.seq (clauseLoop src) reset)

def clauseCost (C : ShortCNF.Clause) : ℕ := (C.map (fun l => 2 * l.1 + 6)).sum

theorem clauseLoop_executes (base : K → List Bool) (src : K) (C : ShortCNF.Clause)
    (tail : List Bool) (a : Aux) :
    Executes (clauseLoop src)
      (store base src (ShortCNF.encodeClause C ++ tail).tail a (ShortCNF.encodeClause C ++ tail).head?)
      (store base src tail a (some false)) (clauseCost C + 1) := by
  induction C with
  | nil => exact Executes.loop_false rfl
  | cons l C ih =>
    have hbody := Executes.seq
      (skipLiteral_executes base src l (ShortCNF.encodeClause C ++ tail) a (some true))
      (read_store base src (ShortCNF.encodeClause C ++ tail) a none)
    have h := Executes.loop_true (p := .seq (skipLiteral src) (read src))
      (b := fun s : Aux × Option Bool => s.2 == some true) rfl hbody ih
    convert! h using 1 <;>
      simp [clauseLoop, ShortCNF.encodeClause, ShortCNF.encodeList, clauseCost, List.append_assoc] <;> omega

theorem skipClause_executes (base : K → List Bool) (src : K) (C : ShortCNF.Clause)
    (tail : List Bool) (a : Aux) (b : Option Bool) :
    Executes (skipClause src) (store base src (ShortCNF.encodeClause C ++ tail) a b)
      (store base src tail a none) (clauseCost C + 3) := by
  have h := Executes.seq (read_store base src _ a b)
    (Executes.seq (clauseLoop_executes base src C tail a)
      (reset_executes base src tail a (some false)))
  convert! h using 1 <;> omega

theorem clauseCost_length (C : ShortCNF.Clause) :
    clauseCost C + 2 = 2 * (ShortCNF.encodeClause C).length := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [clauseCost, List.map_cons, List.sum_cons, ShortCNF.encodeClause,
      ShortCNF.encodeList, List.length_cons, List.length_append, ShortCNF.encodeLiteral,
      List.length_replicate, List.length_nil] at *
    omega

/-- The scanner discards one encoded clause in linear time, including all
unary indices, and preserves every other stack and the auxiliary control. -/
theorem skipClause_linear (base : K → List Bool) (src : K) (C : ShortCNF.Clause)
    (tail : List Bool) (a : Aux) (b : Option Bool) :
    Executes (skipClause src) (store base src (ShortCNF.encodeClause C ++ tail) a b)
      (store base src tail a none) (2 * (ShortCNF.encodeClause C).length + 1) := by
  convert! skipClause_executes base src C tail a b using 1
  have := clauseCost_length C
  omega

end Lax762056Proofs.CNFScan
