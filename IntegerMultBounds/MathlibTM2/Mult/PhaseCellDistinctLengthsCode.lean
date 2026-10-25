module

public import IntegerMultBounds.MathlibTM2.Fast.TableBounds
public import Mathlib.Data.List.Dedup

/-! Structurally emit positive distinct table values in last-occurrence order.
This is a checked table program, not a supplied deduplication certificate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def emitDistinctLength {n : ℕ} (zero i : Fin n) : List (Fin n) → TblCode n
  | [] => .ite zero i (.ins (.emit i zero)) (.ins (.copy zero zero))
  | j::js => .ite i j (emitDistinctLength zero i js)
      (.ite j i (emitDistinctLength zero i js) (.ins (.copy zero zero)))

theorem emitDistinctLength_do {n A W e : ℕ} (zero i : Fin n) (js : List (Fin n))
    (st : TblSt n A) (hz : st.val zero = 0) :
    TblDo A W e (emitDistinctLength zero i js) st (fun st' => st'.val = st.val ∧
      st'.acc = (if 0 < st.val i ∧ st.val i ∉ js.map st.val then tblPairs A e (st.val i) 0 else []).reverse ++ st.acc)
      (2*js.length+2) := by
  induction js with
  | nil =>
    by_cases hp : 0 < st.val i
    · exact TblDo.iteT (by omega : st.val zero < st.val i)
        (TblDo.ins (.emit i zero) (by simp [TblIns.run, hz, hp]))
    · exact TblDo.iteF (by omega : ¬ st.val zero < st.val i)
        (TblDo.ins (.copy zero zero) (by simp [TblIns.run, hp]))
  | cons j js ih =>
    by_cases hlt : st.val i < st.val j
    · exact (TblDo.iteT hlt ih).mono
        (fun st' hh => by simpa [List.map_cons, show st.val i ≠ st.val j by omega] using hh) (by simp <;> omega)
    by_cases hgt : st.val j < st.val i
    · exact (TblDo.iteF hlt (TblDo.iteT hgt ih)).mono
        (fun st' hh => by simpa [List.map_cons, show st.val i ≠ st.val j by omega] using hh) (by simp <;> omega)
    · have he : st.val i = st.val j := by omega
      exact (TblDo.iteF hlt (TblDo.iteF hgt (TblDo.ins (.copy zero zero)
        (P := fun st' => st'.val = st.val ∧ st'.acc = st.acc) (by simp [TblIns.run])))).mono
        (fun st' hh => by simpa [List.map_cons, he] using hh) (by simp <;> omega)

def distinctLengthsCode {n : ℕ} (zero : Fin n) : List (Fin n) → TblCode n
  | [] => .ins (.copy zero zero)
  | i::is => emitDistinctLength zero i is ;; distinctLengthsCode zero is

theorem distinctLengthsCode_do {n A W e : ℕ} (zero : Fin n) (is : List (Fin n))
    (st : TblSt n A) (hz : st.val zero = 0) :
    TblDo A W e (distinctLengthsCode zero is) st (fun st' => st'.val = st.val ∧
      st'.acc = (((is.map st.val).dedup.filter (fun L => decide (0 < L))).flatMap
        (fun L => tblPairs A e L 0)).reverse ++ st.acc) (is.length*(is.length+1)+1) := by
  induction is generalizing st with
  | nil => simpa [distinctLengthsCode] using
      (TblDo.ins (A := A) (W := W) (w := e) (.copy zero zero)
        (st := st) (P := fun st' => st'.val = st.val ∧ st'.acc = st.acc) (by simp [TblIns.run]))
  | cons i is ih =>
    have hc : TblDo A W e (emitDistinctLength zero i is ;; distinctLengthsCode zero is) st
        (fun st' => st'.val = st.val ∧ st'.acc =
          ((((i::is).map st.val).dedup.filter (fun L => decide (0 < L))).flatMap
            (fun L => tblPairs A e L 0)).reverse ++ st.acc)
        ((2*is.length+2)+(is.length*(is.length+1)+1)) := (emitDistinctLength_do (A := A) (W := W) (e := e) zero i is st hz).seq
      (fun st₁ ⟨hv₁, ha₁⟩ => (ih st₁ (by simpa only [hv₁] using hz)).mono
        (fun st₂ ⟨hv₂, ha₂⟩ => by
          refine ⟨hv₂.trans hv₁, ?_⟩
          rw [ha₂, hv₁, ha₁]
          by_cases hm : st.val i ∈ is.map st.val
          · simp [List.dedup_cons, hm]
          · by_cases hp : 0 < st.val i <;>
              simp [List.dedup_cons, hm, hp, List.reverse_append, List.append_assoc]) le_rfl)
    exact hc.mono (fun _ hh => hh) (by simp only [List.length_cons]; nlinarith)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
