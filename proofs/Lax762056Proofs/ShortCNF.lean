import Lax762056Proofs.ThreeSAT

/-! Interface for the short clauses produced by the pending Cook–Levin
circuit compiler. Both the variable and clause bounds are the binary input
length; extra clauses are tautologies. This avoids a separate maximum-index
computation in the eventual machine. -/

namespace Lax762056Proofs.ShortCNF

abbrev Literal := ℕ × Bool
abbrev Clause := List Literal
abbrev Formula := List Clause

def encodeList {α : Type} (encode : α → List Bool) : List α → List Bool
  | [] => [false]
  | x :: xs => true :: (encode x ++ encodeList encode xs)

def encodeLiteral (l : Literal) : List Bool := List.replicate l.1 true ++ [false, l.2]
def encodeClause : Clause → List Bool := encodeList encodeLiteral
def encode : Formula → List Bool := encodeList encodeClause

def eval (ρ : ℕ → Bool) (l : Literal) : Bool := if l.2 then ρ l.1 else !ρ l.1
def Satisfiable (F : Formula) : Prop := ∃ ρ, ∀ C ∈ F, C.any (eval ρ) = true
def Short (F : Formula) : Prop := ∀ C ∈ F, 1 ≤ C.length ∧ C.length ≤ 3

theorem list_length_lt {α : Type} (enc : α → List Bool) (xs : List α) :
    xs.length < (encodeList enc xs).length := by
  induction xs with
  | nil => simp [encodeList]
  | cons x xs ih => simp only [encodeList, List.length_cons, List.length_append]; omega

theorem member_length_lt {α : Type} (enc : α → List Bool) (xs : List α)
    (x : α) (hx : x ∈ xs) : (enc x).length < (encodeList enc xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [encodeList, List.length_cons, List.length_append]
    rcases hx with rfl | hx
    · omega
    · have := ih hx; omega

theorem index_lt (F : Formula) (C : Clause) (l : Literal) (hC : C ∈ F) (hl : l ∈ C) :
    l.1 < (encode F).length := by
  have h₁ := member_length_lt encodeClause F C hC
  have h₂ := member_length_lt encodeLiteral C l hl
  have h₃ : l.1 < (encodeLiteral l).length := by simp [encodeLiteral]
  exact h₃.trans (h₂.trans h₁)

theorem encode_pos (F : Formula) : 0 < (encode F).length :=
  Nat.zero_le F.length |>.trans_lt (list_length_lt _ _)

def boundLiteral (n : ℕ) (hn : 0 < n) (l : Literal) : NAEMaxCut.Literal n :=
  (if h : l.1 < n then ⟨l.1, h⟩ else ⟨0, hn⟩, l.2)

def triple {n : ℕ} (zero : Fin n) (C : List (NAEMaxCut.Literal n)) :
    Fin 3 → NAEMaxCut.Literal n :=
  match C with
  | [] => ![(zero, true), (zero, false), (zero, true)]
  | [a] => ![a, a, a]
  | [a, b] => ![a, b, b]
  | a :: b :: c :: _ => ![a, b, c]

theorem triple_eval {n : ℕ} (zero : Fin n) (ρ : Fin n → Bool)
    (C : List (NAEMaxCut.Literal n)) (h₁ : 1 ≤ C.length) (h₃ : C.length ≤ 3) :
    (NAEMaxCut.eval ρ (triple zero C 0) || NAEMaxCut.eval ρ (triple zero C 1) ||
      NAEMaxCut.eval ρ (triple zero C 2)) = C.any (NAEMaxCut.eval ρ) := by
  rcases C with _ | ⟨a, C⟩
  · simp at h₁
  rcases C with _ | ⟨b, C⟩
  · simp [triple]
  rcases C with _ | ⟨c, C⟩
  · simp [triple, Bool.or_assoc]
  have hnil : C = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_cons] at h₃
    omega
  subst C
  simp [triple, Bool.or_assoc]

def toThreeSAT (F : Formula) : NAEMaxCut.Formula (encode F).length (encode F).length := fun i =>
  if h : i.val < F.length then
    triple ⟨0, encode_pos F⟩ ((F[i]).map (boundLiteral _ (encode_pos F)))
  else triple ⟨0, encode_pos F⟩ []

theorem boundLiteral_eval (n : ℕ) (hn : 0 < n) (ρ : ℕ → Bool) (l : Literal) (hl : l.1 < n) :
    NAEMaxCut.eval (fun v => ρ v.val) (boundLiteral n hn l) = eval ρ l := by
  simp [boundLiteral, hl, eval, NAEMaxCut.eval]

theorem any_congr_mem {α : Type*} (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = q x) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem toThreeSAT_correct (F : Formula) (hF : Short F) :
    Satisfiable F ↔ ThreeSAT.Satisfiable (toThreeSAT F) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    refine ⟨fun v => ρ v.val, ?_⟩
    intro i
    unfold toThreeSAT
    split
    · rename_i hi
      have hmem : F[i.val] ∈ F := List.getElem_mem _
      rw [triple_eval _ _ _ (by simpa using (hF _ hmem).1) (by simpa using (hF _ hmem).2)]
      rw [List.any_map]
      have heq : ∀ l ∈ F[i.val],
          NAEMaxCut.eval (fun v => ρ v.val) (boundLiteral _ (encode_pos F) l) = eval ρ l :=
        fun l hl => boundLiteral_eval _ _ _ _ (index_lt _ _ _ hmem hl)
      exact (any_congr_mem _ _ _ heq).trans (hρ _ hmem)
    · simp [triple, NAEMaxCut.eval]
  · rintro ⟨ρ, hρ⟩
    let assignment : ℕ → Bool := fun v => if h : v < (encode F).length then ρ ⟨v, h⟩ else false
    refine ⟨assignment, ?_⟩
    intro C hC
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hC
    let j : Fin (encode F).length := ⟨i.val, i.isLt.trans (list_length_lt _ _)⟩
    have hj := hρ j
    simp only [toThreeSAT, j, i.isLt, dif_pos] at hj
    rw [triple_eval _ _ _ (by simpa using (hF _ hC).1) (by simpa using (hF _ hC).2), List.any_map] at hj
    have heq : ∀ l ∈ F.get i,
        NAEMaxCut.eval ρ (boundLiteral _ (encode_pos F) l) = eval assignment l := by
      intro l hl
      have hlt := index_lt _ _ _ hC hl
      simp [boundLiteral, hlt, eval, NAEMaxCut.eval, assignment]
    exact (any_congr_mem _ _ _ heq).symm.trans hj

def toMaxCut (F : Formula) : Lax762056.GraphEncoding.Instance := ThreeSAT.toMaxCut (toThreeSAT F)

theorem maxCut_correct (F : Formula) (hF : Short F) :
    Satisfiable F ↔ (toMaxCut F).threshold ≤ Lax762056.MaxCut.maxCut (toMaxCut F).graph :=
  (toThreeSAT_correct F hF).trans (ThreeSAT.maxCut_correct _)

theorem maxCut_order (F : Formula) : (toMaxCut F).order = 20 * (encode F).length + 4 := by
  rw [toMaxCut, ThreeSAT.maxCut_order]
  omega

theorem maxCut_threshold (F : Formula) : (toMaxCut F).threshold = 22 * (encode F).length + 3 := by
  rw [toMaxCut, ThreeSAT.maxCut_threshold]
  omega

end Lax762056Proofs.ShortCNF
