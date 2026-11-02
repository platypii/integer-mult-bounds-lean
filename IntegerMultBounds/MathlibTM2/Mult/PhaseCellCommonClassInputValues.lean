module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonCoreJob

/-! Common dimensions form a shared six-parameter prefix and six class values.
Prefix lookup is structural, independent of the number of jobs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
namespace ComputedClassBanks

def commonInputValues (p u l target s t B W N radius H : ℕ) : Fin 12 → ℕ :=
  Matrix.vecAppend rfl ![p,u,l,target,s,t] ![B,W,N,radius,H-2*radius,H]

theorem commonInputValues_prefix (p u l target s t B W N radius H : ℕ) (i : Fin 6) :
    commonInputValues p u l target s t B W N radius H (Fin.castLE (by decide : 6 ≤ 12) i) =
      ![p,u,l,target,s,t] i := by
  rw [commonInputValues,Matrix.vecAppend_eq_ite]
  simp only [Fin.coe_castLE,dite_eq_left i.isLt]

theorem masterInput_prefix {A s : ℕ} [NeZero s] (r : PackedNormalizedJob A s) (i : Fin 6) :
    r.masterInput.values (Fin.castLE (by decide : 6 ≤ 8) i) = ![r.p,r.u,r.l,r.targetOut,s,r.t] i := by
  have hv : Matrix.vecAppend (by decide : 8 = 6+2) ![r.p,r.u,r.l,r.targetOut,s,r.t] ![r.a,r.b] =
      ![r.p,r.u,r.l,r.targetOut,s,r.t,r.a,r.b] := by
    simp only [Matrix.cons_vecAppend,Matrix.empty_vecAppend]
  change ![r.p,r.u,r.l,r.targetOut,s,r.t,r.a,r.b] (Fin.castLE (by decide : 6 ≤ 8) i) = _
  rw [←hv,Matrix.vecAppend_eq_ite]
  simp only [Fin.coe_castLE,dite_eq_left i.isLt]

theorem commonInputVolume_eq (p u l target s t B W N radius H : ℕ) :
    inputVolume (commonInputValues p u l target s t B W N radius H) =
      2*p+u+l+target+s+t+3*B+W+N+radius+(H-2*radius)+H := by
  simp [inputVolume,inputAssignments,commonInputValues,Matrix.vecAppend_eq_ite]
  ring

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
