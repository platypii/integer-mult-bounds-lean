module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedStandardBoundaryCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardSeamCountPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTablePairRetirement
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredStandardBoundaryCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryCounters

/-! Concrete seed initialization in the existing bank. Retained binary masters
55--57, width ruler 58 and empty zero source 59 are outside the metadata table. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix BoundaryCropMetadata
variable {Q A : ℕ} {P U : Type}

def standardBoundaryMasterPreparation (last : Bool) (cropCount : Fin 117) : Pr P 117 Q A U :=
  .seq (preparedStandardBoundaryCounters last) (standardSeamCountPreparation cropCount)

theorem standardBoundaryMasterPreparation_native (last : Bool) (cropCount : Fin 117) :
    mnNativePushBound 3 (standardBoundaryMasterPreparation (P := P) (Q := Q) (A := A) (U := U) last cropCount) := by
  exact ⟨preparedStandardBoundaryCounters_native last,
    ⟨mnNativePushBound_mono (by decide) (copyWordHeaders_native (T := 117) (P := P) (Q := Q) (A := A) (U := U) 27 28 [(cropCount,54)]).1,
      mnNativePushBound_mono (by decide) (unaryProduct_native 15 54 19 27 28)⟩⟩

def standardBoundaryMasterState (cropCount : Fin 117) (N narrowWidth s width k W : ℕ)
    (S : Stacks 117 A) : Stacks 117 A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    26 (List.replicate (coreStart width k*W) tick))
    24 (List.replicate (coreLength s width k*W) tick)) 54 (S.R cropCount))
    19 (List.replicate (N*coreLength s width k*narrowWidth) tick))}

theorem standardBoundaryMasterState_lengths (cropCount : Fin 117)
    (N narrowWidth s width k W : ℕ) (S : Stacks 117 A) :
    let F := standardBoundaryMasterState cropCount N narrowWidth s width k W S
    (F.R 26).length = coreStart width k*W ∧
    (F.R 24).length = coreLength s width k*W ∧
    (F.R 19).length = N*coreLength s width k*narrowWidth := by
  simp [standardBoundaryMasterState]

theorem standardBoundaryMasterState_off (cropCount : Fin 117)
    (N narrowWidth s width k W : ℕ) (S : Stacks 117 A) (i : Fin 117)
    (hi : i ∉ [(26:Fin 117),24,54,19]) :
    (standardBoundaryMasterState cropCount N narrowWidth s width k W S).R i = S.R i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  simp [standardBoundaryMasterState,Function.update_of_ne,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]

theorem standardBoundaryMasterState_fresh (cropCount : Fin 117)
    (N narrowWidth s width k W : ℕ) (S : Stacks 117 A)
    (hfresh : ∀ i ∈ standardSeamPublicationPlan.support,
      i ≠ standardSeamPublicationPlan.advances → S.R i = []) :
    ∀ i ∈ standardSeamPublicationPlan.support, i ≠ standardSeamPublicationPlan.advances →
      (standardBoundaryMasterState cropCount N narrowWidth s width k W S).R i = [] := by
  intro i hi hne
  rw [standardBoundaryMasterState_off cropCount N narrowWidth s width k W S i]
  · exact hfresh i hi hne
  · have hd : List.Disjoint standardSeamPublicationPlan.support [(26:Fin 117),24,54,19] := by simp [List.disjoint_left,standardSeamPublicationPlan,PreparedPublicationPlan.support]
    exact List.disjoint_left.mp hd hi

theorem standardBoundaryMasterPreparation_exec (body : P → Pr P 117 Q A U)
    (last : Bool) (cropCount : Fin 117)
    (hreg : [cropCount,15,54,19,27,28,24,26].Nodup) (N narrowWidth : ℕ) (D s width W : ℕ)
    (hwidthPos : 0 < width) (hwordPos : 0 < W) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidth : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j)))
    (hblank : ∀ r, S.R (boundaryCounterRegister r) = [])
    (hmasters : S.R 26 = [] ∧ S.R 24 = [])
    (hN : (S.R 15).length = N)
    (hbits : (S.R cropCount).length = coreLength s width (index last s width)*narrowWidth)
    (hcountBlank : S.R 54 = [] ∧ S.R 19 = [] ∧ S.R 27 = [] ∧ S.R 28 = []) (depth : ℕ) :
    let L := coreLength s width (index last s width)
    ∃ v' n, v'.user = v.user ∧
      n ≤ (64*D+81)+(16*tblC D 0+6*(s*W)+22*D+13)+(20*D+21)+
        ((6*(L*narrowWidth)+6)+(N*(4*(L*narrowWidth)+9)+4)) ∧
      Exec body (standardBoundaryMasterPreparation last cropCount)
        (mk v S) n (mk v' (standardBoundaryMasterState cropCount N narrowWidth s width (index last s width) W S)) := by
  dsimp only
  obtain ⟨u,n,hu,hn,he⟩ := preparedStandardBoundaryCounters_exec body last D s width W
    hwidthPos hwordPos hroom hvolumeFit value hvalues hfit v S hwidth hzero hwords hblank hmasters depth
  obtain ⟨h54,h19,h27,h28⟩ := hcountBlank
  have hr := hreg
  regs_ne hr
  let M : Stacks 117 A := {S with R := (Function.update (Function.update S.R 26
    (List.replicate (coreStart width (index last s width)*W) tick)) 24
    (List.replicate (coreLength s width (index last s width)*W) tick))}
  obtain ⟨v',m,hv,hm,hex⟩ := standardSeamCountPreparation_exec (body := body) cropCount
    (by regs_nodup) N (coreLength s width (index last s width)) narrowWidth u M
    (by simpa [M] using hN)
    (by simpa [M,Function.update_of_ne, *,Ne.symm] using hbits)
    (by simp [M,h54,h19,h27,h28])
  refine ⟨v',n+m,hv.trans hu,by omega,?_⟩
  simpa [standardBoundaryMasterPreparation,standardBoundaryMasterState,M,Function.update_of_ne, *,Ne.symm] using Exec.seq he hex

theorem standardBoundaryMasterPreparation_within (last : Bool) (cropCount : Fin 117)
    (v v' : HS 117 Q A U) (S F : Stacks 117 A) (n depth : ℕ)
    (he : Exec body (standardBoundaryMasterPreparation last cropCount) (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*n) depth
      (standardBoundaryMasterPreparation last cropCount) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 3 (standardBoundaryMasterPreparation_native last cropCount) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
