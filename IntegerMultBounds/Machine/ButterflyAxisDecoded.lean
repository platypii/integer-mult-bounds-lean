import IntegerMultBounds.Machine.ButterflyAxisSemantics

/-! Exact complex semantics of the physical selected-axis schedule. The
mathematical operator is the genuine two-point complex butterfly, with its
coordinate pairing specified by the same finite product indexing used by the
proved tape split and merge. -/
namespace IntegerMultBounds.Machine.ButterflyAxisDecoded
noncomputable section
open ButterflyAxisArray ButterflyAxisSemantics ButterflyStreamSemantics
open ButterflyAxisSerialization ButterflyAxisHeadersGeometry ButterflyAxisHeadersData
open RecursiveInterchangeRows (pack)

/-- The two output coordinates of the forward complex butterfly. -/
def butterfly (k : Fin 2) (a b : ℂ) : ℂ :=
  if k=0 then (a+b+Complex.I*(a-b))/2 else (a+b-Complex.I*(a-b))/2

def view {α : Type*} (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → α)
    (h : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)))
    (j : Fin 2) (k : Fin (lower t R)) : α :=
  f (Fin.cast (size_eq D t R p ht) (pack h (pack j k)))

def join {α : Type*} (D t R p : ℕ) (ht : t<D)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)) → Fin 2 → Fin (lower t R) → α)
    (i : Fin (Size D R)) : α :=
  let hjk := finProdFinEquiv.symm (Fin.cast (size_eq D t R p ht).symm i)
  let jk := finProdFinEquiv.symm hjk.2
  xs hjk.1 jk.1 jk.2

def axis (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → ℂ) : Fin (Size D R) → ℂ :=
  join D t R p ht (fun h j k => butterfly j (view D t R p ht f h 0 k) (view D t R p ht f h 1 k))

def decoded (D R p j : ℕ) (f : Array D R) : Fin (Size D R) → ℂ :=
  fun i => decode (ButterflyGuard.halfWidth p D) (p+j) (f i)

theorem result_decode (a b : ButterflyStreamData.Coefficient) (p D j : ℕ) (hj : j≤D)
    (ha : a.1.length=ButterflyGuard.width p D ∧ a.2.length=ButterflyGuard.width p D)
    (hb : b.1.length=ButterflyGuard.width p D ∧ b.2.length=ButterflyGuard.width p D)
    (hga : Networks.GaussianPrecision.BoundedGrid (p+j) (2^p*4^j)
      (decode (ButterflyGuard.halfWidth p D) (p+j) a))
    (hgb : Networks.GaussianPrecision.BoundedGrid (p+j) (2^p*4^j)
      (decode (ButterflyGuard.halfWidth p D) (p+j) b)) (k : Fin 2) :
    decode (ButterflyGuard.halfWidth p D) (p+(j+1)) (ButterflyStreamData.result a b k)=
      butterfly k (decode (ButterflyGuard.halfWidth p D) (p+j) a)
        (decode (ButterflyGuard.halfWidth p D) (p+j) b) := by
  have hh := result_exact a b p D j hj ha hb hga hgb
  fin_cases k
  · simpa [butterfly,Nat.add_assoc] using hh.1
  · simpa [butterfly,Nat.add_assoc] using hh.2

theorem decoded_apply (D t R p j : ℕ) (ht : t<D) (hj : j≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p j f) :
    decoded D R p (j+1) (applyAxis D t R p ht f)=axis D t R p ht (decoded D R p j f) := by
  funext i
  unfold decoded applyAxis unshape joined transformed axis join view reshape
  exact result_decode _ _ p D j hj (hw _) (hw _) (hg _) (hg _) _

def complexStep (D t R p : ℕ) (f : Fin (Size D R) → ℂ) : Fin (Size D R) → ℂ :=
  if ht : t<D then axis D t R p ht f else f

def complexRun (D start R p : ℕ) : ℕ → (Fin (Size D R) → ℂ) → (Fin (Size D R) → ℂ)
  | 0,f => f
  | n+1,f => complexStep D (start+n) R p (complexRun D start R p n f)

/-- Decoding the actual counted machine result equals the successive complex
axis operators, at precisely one extra dyadic precision bit per physical pass. -/
theorem decoded_run (D start R p n : ℕ) (hfit : start+n≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p 0 f) :
    decoded D R p n (ButterflyAxisSchedule.run D start R p n f)=
      complexRun D start R p n (decoded D R p 0 f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht : start+n<D := by omega
    simp only [ButterflyAxisSchedule.run,ButterflyAxisSchedule.step,dite_eq_left ht,complexRun,complexStep]
    rw [decoded_apply D (start+n) R p n ht (by omega) _
      (ButterflyAxisSchedule.width_run D start R p n f hw)
      (grid_run D start R p n (by omega) f hw hg),ih (by omega)]

/-- A normalized input alone establishes every grid hypothesis used by the
literal machine's exact arithmetic semantics. -/
theorem decoded_run_normalized (D start R p n : ℕ) (hfit : start+n≤D)
    (f : Array D R) (hw : Width D R p f)
    (hn : ∀ i, ‖decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1) :
    decoded D R p n (ButterflyAxisSchedule.run D start R p n f)=
      complexRun D start R p n (decoded D R p 0 f) :=
  decoded_run D start R p n hfit f hw (grid_initial D R p f hn)

end
end IntegerMultBounds.Machine.ButterflyAxisDecoded
