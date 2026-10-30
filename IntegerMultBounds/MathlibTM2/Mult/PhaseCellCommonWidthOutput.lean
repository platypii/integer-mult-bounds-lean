module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketWidthControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDerivedInverseRoundBatch

/-! Generated numerical rounding followed by signed common-width publication. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.LayerMachine

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

def commonWidthOutput : Pr P 303 Q A U :=
  .seq inverseRoundBatch (generatedWidenPackets 11 12 132 4 13 14)

/-- Numerical output bounds justify sign extension after generated rounding.
All scalar state and retained headers restore; only output source 132 changes. -/
theorem commonWidthOutput_exec (hA : 4 ≤ A) {p u l target s t a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (wl : List (Fin (A+4))) (hwl : wl.length = inverseCallerWordWidth p u l target s t)
    (W : ℕ) (hW : 2*p+13 ≤ W) (xs : List GaussianInt)
    (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds familyInverseScalarReg S
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,13,14] : List (Fin 303)), S.R r = [])
    (hwide : (S.R 11).length = W) (hword : (S.R 12).length = 2*p+13) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let q := 4*E
    let j := inverseNormalizationShift p
    (∀ z ∈ xs, ‖value q (symZ w z)‖ ≤ 8*(2 : ℝ)^(p+8)) →
    S.R 132 = cstream A w xs →
    ∃ v' n, v'.user = v.user ∧
      n ≤ inverseRoundBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length+
        (4*W+4*(2*p+13)+2*(W-(2*p+13))+(xs.length*(6*W+10)+4)+10) ∧
      Exec body commonWidthOutput (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A W (xs.map (finalRoundWord w q p j))))}) := by
  dsimp only
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let w := 8*E+8
  let q := 4*E
  let j := inverseNormalizationShift p
  intro hbound hsrc
  have hpq : p ≤ q := by dsimp [q,E,inverseExecutionExponent]; omega
  let ys := xs.map (finalRoundWord w q p j)
  have hfit : ∀ z ∈ ys, TopFitsZ (2*p+13) z := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    have hf := finalRound_fits q p j (p+8) (2*p+13) hpq (by omega) (symZ w x) (hbound x hx)
    exact ⟨⟨(abs_lt.mp hf.1).1.le,(abs_lt.mp hf.1).2⟩,
      ⟨(abs_lt.mp hf.2).1.le,(abs_lt.mp hf.2).2⟩⟩
  have hblank₀ : ∀ r ∈ ([0,1,2,3,4,5,6,7,8] : List (Fin 303)), S.R r = [] := by
    intro r hr
    exact hblank r (List.mem_append_left [13,14] hr)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := inverseRoundBatch_derived_exec (body := body) hA
    hst ha hb hband wl hwl xs v S hS hblank₀ hsrc
  let S₁ : Stacks 303 A := {S with R := Function.update S.R 132 (cstream A (2*p+13) ys)}
  obtain ⟨v₂,hu₂,he₂⟩ := generatedWidenPackets_exec (body := body)
    (show [(11 : Fin 303),12,132,4,13,14].Nodup by decide)
    (2*p+13) W (by omega) hW ys hfit v₁ S₁
    (by simpa [S₁] using hwide) (by simpa [S₁] using hword) (by simp [S₁])
    (by simpa [S₁] using hblank 4 (by decide))
    (by simpa [S₁] using hblank 13 (by decide))
    (by simpa [S₁] using hblank 14 (by decide))
  refine ⟨v₂,_,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · simpa only [ys,List.length_map] using Nat.add_le_add_right hn₁
      (4*W+4*(2*p+13)+2*(W-(2*p+13))+(xs.length*(6*W+10)+4)+10)
  · apply congrArg (mk v₂)
    simp only [S₁,Function.update_idem]
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
