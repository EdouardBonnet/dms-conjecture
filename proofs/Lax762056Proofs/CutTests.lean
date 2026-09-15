import Lax762056Proofs.CutEndpoints
import Lax762056Proofs.CNFMachine

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace Lax762056Proofs.CutTests

open CutVertices CNFAtom

@[simp] theorem value_constant {k : ℕ} (b : Bool) (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) : value (.constant b) F v = b := rfl

def mapVariable {k n : ℕ} (v : Fin k → Fin n) : Variable k → Variable n
  | .inl (aux, x) => .inl (aux, v x)
  | .inr _ => .inr ()

def mapCore {k n : ℕ} (v : Fin k → Fin n) (x : Variable k × Bool) : Variable n × Bool :=
  (mapVariable v x.1, x.2)

def mapOccurrence {k n : ℕ} (v : Fin k → Fin n) : Occurrence k → Occurrence n
  | .inl x => .inl (mapVariable v x)
  | .inr (i, b, e) => .inr (v i, b, e)

def mapPoint {k n : ℕ} (v : Fin k → Fin n) : Point k → Point n
  | .inl x => .inl (mapCore v x)
  | .inr (e, b) => .inr (mapOccurrence v e, b)

inductive Description (k : ℕ)
  | known (x : Variable k × Bool)
  | lookup (clause : Fin k) (slot : Fin 3)

def describeLiteral {k : ℕ} (i : Fin k) (second : Bool) (j : Fin 3) : Description k :=
  if second then
    if j = 0 then .known (.inl (true, i), false)
    else if j = 1 then .lookup i 2 else .known (.inr (), true)
  else
    if j = 0 then .lookup i 0
    else if j = 1 then .lookup i 1 else .known (.inl (true, i), true)

def describe {k : ℕ} : Occurrence k → Bool → Description k
  | .inl v, b => .known (v, b)
  | .inr (i, second, edge), b => describeLiteral i second (CutEndpoints.slot edge b)

def evaluateDescription {k n : ℕ} (C : NAEMaxCut.Formula n n) (v : Fin k → Fin n) :
    Description k → Variable n × Bool
  | .known x => mapCore v x
  | .lookup i j => CutEndpoints.original (C (v i) j)

theorem describe_correct {k n : ℕ} (C : NAEMaxCut.Formula n n) (v : Fin k → Fin n)
    (e : Occurrence k) (b : Bool) :
    evaluateDescription C v (describe e b) = CutEndpoints.endpoint C (mapOccurrence v e) b := by
  rcases e with x | ⟨i, second, edge⟩
  · rfl
  · cases second <;> fin_cases edge <;> cases b <;> rfl

def variableTest {k : ℕ} : Variable k → Variable k → Test k
  | .inl (a, x), .inl (b, y) => if a = b then .equal x y else .constant false
  | .inr _, .inr _ => .constant true
  | _, _ => .constant false

def knownTest {k : ℕ} (x y : Variable k × Bool) : Test k :=
  if x.2 = y.2 then variableTest x.1 y.1 else .constant false

def coreTest {k : ℕ} (x : Variable k × Bool) : Description k → Test k
  | .known y => knownTest x y
  | .lookup i j => match x.1 with
    | .inl (false, a) => .literal i a j x.2
    | _ => .constant false

def occurrenceTest {k : ℕ} : Occurrence k → Occurrence k → Test k
  | .inl x, .inl y => variableTest x y
  | .inr (i, b, e), .inr (j, d, f) => if b = d ∧ e = f then .equal i j else .constant false
  | _, _ => .constant false

def adjacentTest {k : ℕ} : Point k → Point k → Test k
  | .inl _, .inl _ => .constant false
  | .inl x, .inr (e, b) => coreTest x (describe e b)
  | .inr (e, b), .inl x => coreTest x (describe e b)
  | .inr (e, b), .inr (f, d) => if b = d then .constant false else occurrenceTest e f

theorem variableTest_correct {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (x y : Variable k) :
    value (variableTest x y) F v = decide (mapVariable v x = mapVariable v y) := by
  rcases x with ⟨a, x⟩ | u <;> rcases y with ⟨b, y⟩ | w
  · cases a <;> cases b <;> simp [variableTest, value, mapVariable]
  all_goals simp [variableTest, value, mapVariable]

theorem knownTest_correct {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (x y : Variable k × Bool) :
    value (knownTest x y) F v = decide (mapCore v x = mapCore v y) := by
  by_cases h : x.2 = y.2 <;> simp [knownTest, h, variableTest_correct, mapCore, Prod.ext_iff]

theorem coreTest_correct {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (x : Variable k × Bool) (d : Description k) :
    value (coreTest x d) F v = decide (mapCore v x = evaluateDescription (ShortCNF.toThreeSAT F) v d) := by
  cases d with
  | known y => exact knownTest_correct F v x y
  | lookup i j =>
    rcases x with ⟨(⟨aux, a⟩ | u), sign⟩
    · cases aux
      · have hs := CNFLookup.selected_correct F (v i) j
        have hb := CNFLookup.selected_bound F (v i).val j
        simp [coreTest, value, mapCore, mapVariable, evaluateDescription, CutEndpoints.original,
          ← hs, ShortCNF.boundLiteral, hb, Fin.ext_iff, eq_comm, and_comm]
      · simp [coreTest, value, mapCore, mapVariable, evaluateDescription, CutEndpoints.original]
    · simp [coreTest, value, mapCore, mapVariable, evaluateDescription, CutEndpoints.original]

theorem occurrenceTest_correct {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (x y : Occurrence k) :
    value (occurrenceTest x y) F v = decide (mapOccurrence v x = mapOccurrence v y) := by
  rcases x with x | ⟨i, b, e⟩ <;> rcases y with y | ⟨j, d, f⟩
  · simpa [occurrenceTest, mapOccurrence] using! variableTest_correct F v x y
  · simp [occurrenceTest, value, mapOccurrence]
  · simp [occurrenceTest, value, mapOccurrence]
  · by_cases h : b = d ∧ e = f
    · rcases h with ⟨rfl, rfl⟩; simp [occurrenceTest, value, mapOccurrence]
    · simp [occurrenceTest, h, value, mapOccurrence, and_assoc]

theorem adjacentTest_correct {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (x y : Point k) :
    value (adjacentTest x y) F v =
      decide (CutEndpoints.adjacent (ShortCNF.toThreeSAT F) (mapPoint v x) (mapPoint v y)) := by
  rcases x with x | ⟨e, b⟩ <;> rcases y with y | ⟨f, d⟩
  · simp [adjacentTest, mapPoint, CutEndpoints.adjacent]
  · simp [adjacentTest, coreTest_correct F, describe_correct, mapPoint, CutEndpoints.adjacent]
  · simp [adjacentTest, coreTest_correct F, describe_correct, mapPoint, CutEndpoints.adjacent]
  · cases b <;> cases d <;> simp [adjacentTest, occurrenceTest_correct, mapPoint, CutEndpoints.adjacent]

def mapRaw {k n : ℕ} (v : Fin k → Fin n) : Raw k → Raw n
  | .inl (t, x) => .inl (t, v x)
  | .inr t => .inr t

def rawTest {k : ℕ} (x y : Raw k) : Test k := adjacentTest (rawEquiv k x) (rawEquiv k y)

theorem map_rawEquiv {k n : ℕ} (v : Fin k → Fin n) (x : Raw k) :
    mapPoint v (rawEquiv k x) = rawEquiv n (mapRaw v x) := by
  rcases x with ⟨t, x⟩ | t <;> cases t <;> rfl

theorem rawTest_correct {k : ℕ} (F : ShortCNF.Formula)
    (v : Fin k → Fin (ShortCNF.encode F).length) (x y : Raw k) :
    value (rawTest x y) F v = decide ((ShortCNF.toMaxCut F).graph.Adj
      (rawFinEquiv _ (mapRaw v x)) (rawFinEquiv _ (mapRaw v y))) := by
  rw [rawTest, adjacentTest_correct F, map_rawEquiv, map_rawEquiv]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact (CutEndpoints.adjacent_correct (ShortCNF.toThreeSAT F) _ _).symm

end Lax762056Proofs.CutTests
