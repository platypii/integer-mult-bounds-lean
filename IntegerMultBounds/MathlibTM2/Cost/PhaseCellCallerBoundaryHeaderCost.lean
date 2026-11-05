module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundarySeamHeaderCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPreparedBoundaryRetirement

/-! Apply the abstract eleven-word volume identity to the caller's actual
generated boundary controls. Numerical archives and output tails are absent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T A s : ℕ}
noncomputable section

def boundaryTemporaryHeaderVolume (p s width : ℕ) : ℕ :=
  (2*p+13)+boundaryCropHeaderVolume p s width+
    coreStart width (boundaryCropIndex s width 1)*(2*p+13)+
    coreStart width (boundaryCropIndex s width 2)*(2*p+13)

theorem boundaryTemporaryHeaderVolume_le (p s width : ℕ) (hs : 1 ≤ s)
    (hw : 0 < width) (hroom : 3*width < s) :
    boundaryTemporaryHeaderVolume p s width ≤ 6*s*(2*p+13) := by
  have hc := boundaryCropHeaderVolume_le p s width
  have h₁ := Nat.mul_le_mul_right (2*p+13) (boundaryCropStart_le s width hw hroom 1)
  have h₂ := Nat.mul_le_mul_right (2*p+13) (boundaryCropStart_le s width hw hroom 2)
  have hw := Nat.le_mul_of_pos_left (2*p+13) hs
  unfold boundaryTemporaryHeaderVolume
  simp only [Nat.mul_assoc] at hc ⊢
  omega

private theorem callerBoundaryGeometrySkip_length (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) (slot : Fin 3) :
    ((callerBoundaryGeometryState widthSource s width w S).R
      (boundaryGeometryRegister T widthSource (boundarySeamCropSkip slot))).length =
      coreStart width (boundaryCropIndex s width slot)*w := by
  have h := congrArg (fun B : Stacks 117 A => B.R (boundarySeamCropSkip slot))
    (callerBoundaryGeometryState_view widthSource s width w S)
  change (callerBoundaryGeometryState widthSource s width w S).R
    (boundaryGeometryRegister T widthSource (boundarySeamCropSkip slot)) = _ at h
  have hs := h.trans (exportBoundaryGeometryState_skip s width w [0,1,2] (by decide) _ slot
    (by fin_cases slot <;> simp))
  simpa only [List.length_replicate] using congrArg List.length hs

theorem callerPreparedBoundaryClearCost_eq (widthSource : Fin T) (p s width : ℕ)
    (S : Stacks (MachineTapes T) A) :
    let F := callerPreparedBoundaryState widthSource p s width S
    2*((callerPreparedTemporaryHeaders T).map (fun i => (F.R i).length)).sum+
      2*(callerPreparedTemporaryHeaders T).length+1 = 2*boundaryTemporaryHeaderVolume p s width+13 := by
  let F := callerPreparedBoundaryState widthSource p s width S
  let M : Stacks (MachineTapes T) A :=
    {S with R := (Function.update S.R (fullHeader T (.publication 3))
      (List.replicate (2*p+13) IntegerMultBounds.MathlibTM2.Node.tick))}
  have hcounts (slot : Fin 3) : (F.R (fullHeader T (.publication (Fin.castAdd 4 slot)))).length =
      coreLength s width (boundaryCropIndex s width slot)*(2*p+13) := by
    change ((callerBoundaryGeometryState widthSource s width (2*p+13) M).R _).length = _
    rw [callerBoundaryGeometryState_count,List.length_replicate]
  have hword : (F.R (fullHeader T (.publication 3))).length = 2*p+13 := by
    change ((callerBoundaryGeometryState widthSource s width (2*p+13) M).R _).length = _
    rw [callerBoundaryGeometryState_word]
    simp [M]
  have hskip₁ := callerBoundaryGeometrySkip_length widthSource s width (2*p+13) M 1
  have hskip₂ := callerBoundaryGeometrySkip_length widthSource s width (2*p+13) M 2
  rw [boundaryGeometryRegister_skip_one] at hskip₁
  rw [boundaryGeometryRegister_skip_two] at hskip₂
  have hsum : ((callerPreparedTemporaryHeaders T).map (fun i => (F.R i).length)).sum =
      boundaryTemporaryHeaderVolume p s width := by
    simp only [callerPreparedTemporaryHeaders,List.map_ofFn,Function.comp_def]
    norm_num [boundaryTemporaryHeaderVolume,boundaryCropHeaderVolume,List.ofFn_succ,Fin.succ]
    rw [hword,show (F.R (fullHeader T (.publication 0))).length = _ from hcounts 0,
      show (F.R (fullHeader T (.publication 1))).length = _ from hcounts 1,
      show (F.R (fullHeader T (.publication 2))).length = _ from hcounts 2,
      show (F.R (fullHeader T (.publication 4))).length = _ from hskip₁,
      show (F.R (fullHeader T (.publication 5))).length = _ from hskip₂]
    ring
  change 2*((callerPreparedTemporaryHeaders T).map (fun i => (F.R i).length)).sum+
    2*(callerPreparedTemporaryHeaders T).length+1 = _
  rw [hsum]
  simp only [callerPreparedTemporaryHeaders,List.length_ofFn]

theorem callerPreparedBoundaryMasterCopyCosts_eq (p u l target t B W D N radius width : ℕ)
    (src : Fin 11 → Fin T) (widthSource : Fin T)
    (source destination : Fin ((T+headerCount)+175)) (S : Stacks (MachineTapes T) A)
    (hraw : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hD : (S.R (unarySource T widthSource)).length = D)
    (hscalars : ∀ i, S.R (globals T i) = binSyms D (globalValues p u l target s t B W N radius width i)) :
    let F := callerPreparedBoundaryState widthSource p s width S
    let pairs := boundarySeamMasterCopies source destination
      (seamMasterSources T src widthSource)
    ((pairs.map (fun pair => 6*(F.R pair.1).length+6)).sum+1 =
      6*boundarySeamHeaderVolume p s width W D N+67) ∧
    (2*(pairs.map (fun pair => (F.R pair.1).length)).sum+2*pairs.length+1 =
      2*boundarySeamHeaderVolume p s width W D N+23) := by
  dsimp only
  let seedValue := fun i : Fin 117 => if i = 55 then s else if i = 56 then width else W
  have hseed : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j := by
    intro j
    fin_cases j <;> simp [seedValue,boundarySeedGlobals]
  have hwords := callerPreparedBoundaryState_masterWords p u l target t B W D N radius width
    src widthSource seedValue hseed S hraw hD hscalars
    ((callerPreparedBoundaryState widthSource p s width S).R (fullHeader T (.publication 6)))
  simp only [Function.update_eq_self] at hwords
  exact boundarySeamMasterCopyCosts_eq source destination
    (seamMasterSources T src widthSource) _ seedValue hwords

end
end IntegerMultBounds.MathlibTM2.Cost
