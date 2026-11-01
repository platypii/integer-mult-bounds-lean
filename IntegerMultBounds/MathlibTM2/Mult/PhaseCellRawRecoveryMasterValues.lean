module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJobProfiles
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateInverseMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseHeadersReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexRecoveryHeaders

/-! The ordinary inverse scalar generator computes exactly the numerical masters
of the mathematical raw-recovery constructor, including its extra accuracy bit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

noncomputable def recoveryMasterValues {s : ℕ} (H : ReplicaHaloProblem s) : Fin 10 → ℕ :=
  masterHeaderValues (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band H.origin (H.origin+H.span)

def recoveryMasterPort : Fin 10 → Fin 392 := ![114,101,112,108,97,98,99,100,111,113]

theorem complexRecoveryHeader_master {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (W N : ℕ) (i : Fin 10) :
    complexRecoveryHeader H W N (recoveryMasterPort i) = recoveryMasterValues H i := by
  fin_cases i <;> rfl

theorem RawRecoveryJob.ofComplexBounds_masterValues
    {s t p u l target a b V : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := target+1) (rhsExp := 2) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1)
    (W : ℕ) (hW : 2*packedHaloPrecision p l s t u (target+1) 2 a b+8 ≤ W) :
    recoveryMasterValues (RawRecoveryJob.ofComplexBounds bounds Fs hF W hW).problem =
      inverseMasterValues p u l target s t a b := by
  obtain ⟨hp,hl,ht,hu,he,ha,hspan,hband,_,_,_,_,hH⟩ :=
    RawRecoveryJob.ofComplexBounds_profile bounds Fs hF W hW
  have hE := inverseExecutionExponent_eq p u l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
  have hsize := boundaryHaloTarget_sizing p u l (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  simp only [recoveryMasterValues,ReplicaHaloProblem.stage,ReplicaHaloProblem.precision,hp,hl,ht,hu,he,
    ha,hspan,hband,hH,Nat.add_sub_of_le bounds.hab]
  rw [hsize.1,hsize.2.1]
  simp only [masterHeaderValues,inverseMasterValues,executionStagePrecision,executionPrecision,hE]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
