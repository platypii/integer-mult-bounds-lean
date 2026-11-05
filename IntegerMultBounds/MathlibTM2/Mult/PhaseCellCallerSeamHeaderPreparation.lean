module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGenerateBoundaryCounts

/-! Produce the four temporary seam headers from original caller dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def seamHeaderPreparation (precision widthSource : Fin T) : Pr P (MachineTapes T) Q A U :=
  .seq (seamNarrowWidthProgram precision) (callerBoundaryCountsProgram widthSource)

def seamHeadersState (p s width : ℕ) (S : Stacks (MachineTapes T) A) : Stacks (MachineTapes T) A :=
  callerBoundaryCountsState s width (2*p+13)
    {S with R := Function.update S.R (fullHeader T (.publication 3)) (List.replicate (2*p+13) tick)}

theorem seamHeadersState_off (p s width : ℕ) (S : Stacks (MachineTapes T) A)
    (i : Fin (MachineTapes T))
    (hi : ∀ j : Fin 4, i ≠ fullHeader T (.publication (Fin.castAdd 3 j))) :
    (seamHeadersState p s width S).R i = S.R i := by
  have h0 : i ≠ fullHeader T (.publication 0) := hi 0
  have h1 : i ≠ fullHeader T (.publication 1) := hi 1
  have h2 : i ≠ fullHeader T (.publication 2) := hi 2
  have h3 : i ≠ fullHeader T (.publication 3) := hi 3
  simp only [seamHeadersState,callerBoundaryCountsState,Function.update_of_ne h0,
    Function.update_of_ne h1,Function.update_of_ne h2,Function.update_of_ne h3]

theorem seamHeadersState_counts (p s width : ℕ) (S : Stacks (MachineTapes T) A) (slot : Fin 3) :
    ((seamHeadersState p s width S).R (fullHeader T (.publication (Fin.castAdd 4 slot)))).length =
      coreLength s width (boundaryCropIndex s width slot)*(2*p+13) := by
  fin_cases slot <;>
    simp [seamHeadersState,callerBoundaryCountsState,(fullHeader_injective T).eq_iff]

theorem seamHeadersState_narrow (p s width : ℕ) (S : Stacks (MachineTapes T) A) :
    ((seamHeadersState p s width S).R (fullHeader T (.publication 3))).length = 2*p+13 := by
  simp [seamHeadersState,callerBoundaryCountsState,(fullHeader_injective T).eq_iff]

theorem seamHeadersState_masterWords (p u l target s t B W D N radius width : ℕ)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (seedValue : Fin 117 → ℕ)
    (hseed : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (S : Stacks (MachineTapes T) A)
    (hraw : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hD : (S.R (unarySource T widthSource)).length = D)
    (hscalars : ∀ i, S.R (globals T i) = binSyms D (globalValues p u l target s t B W N radius width i)) :
    BoundarySeamHeaderWords (s := s) p width W D N seedValue
      (fun i => (seamHeadersState p s width S).R
        (Fin.castAdd tapeCount (seamMasterSources T src widthSource i))) := by
  have hrawRead (k : Fin T) : (seamHeadersState p s width S).R (unarySource T k) = S.R (unarySource T k) :=
    seamHeadersState_off p s width S _ (fun j => (fullHeader_ne_bank id _ k).symm)
  have hscalarRead (i : Fin 11) : (seamHeadersState p s width S).R (globals T i) = S.R (globals T i) :=
    seamHeadersState_off p s width S _ (fun j => (fullHeader_injective T).ne (by intro h; cases h))
  apply seamMasterSources_headerWords p u l target t B W D N radius width src widthSource seedValue hseed
  · intro i
    exact (congrArg List.length (hrawRead (src i))).trans (hraw i)
  · exact (congrArg List.length (hrawRead widthSource)).trans hD
  · intro i
    exact (hscalarRead i).trans (hscalars i)
  · exact seamHeadersState_narrow p s width S
  · exact seamHeadersState_counts p s width S

theorem seamHeaderPreparation_exec (body : P → Pr P (MachineTapes T) Q A U)
    (precision widthSource : Fin T) (D p s width : ℕ) (hw : 0 < width)
    (hroom : 3*width < s) (hvolumeFit : s*(2*p+13) < 2^D)
    (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hp : (S.R (unarySource T precision)).length = p)
    (hD : (S.R (unarySource T widthSource)).length = D)
    (hs : S.R (globals T 4) = binSyms D s) (hwidth : S.R (globals T 10) = binSyms D width)
    (hblank : ∀ i : Fin 4, S.R (fullHeader T (.publication (Fin.castAdd 3 i))) = [])
    (hprivate : ∀ i : Fin tapeCount, S.R (Fin.natAdd ((T+headerCount)+175) i) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (4*p+5)+((2*p+13)*(4*D+10)+4*D+8)+boundaryCountExportCost D s width (2*p+13)+(2*D+2) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (13*(4*p+5)+2*(4*D+4)+3*boundaryCountExportCost D s width (2*p+13))) depth
        (seamHeaderPreparation precision widthSource) (mk v S) n (mk v' (seamHeadersState p s width S)) := by
  obtain ⟨u,hu,hnarrow⟩ := seamNarrowWidth_exec_within body precision p v S hp (hblank 3) (hprivate _) depth
  let M : Stacks (MachineTapes T) A := {S with R :=
    (Function.update S.R (fullHeader T (.publication 3)) (List.replicate (2*p+13) tick))}
  have hread (i : Fin (MachineTapes T)) (hi : i ≠ fullHeader T (.publication 3)) : M.R i = S.R i := by
    dsimp only [M]
    exact Function.update_of_ne hi _ _
  obtain ⟨v',n,hv,hn,he⟩ := callerBoundaryCounts_exec body widthSource D s width (2*p+13) hw (by omega)
    hroom hvolumeFit u M
    (by exact (congrArg List.length (hread (unarySource T widthSource)
      (fullHeader_ne_bank id (.publication 3) widthSource).symm)).trans hD)
    (by exact (hread (globals T 4) ((fullHeader_injective T).ne (by intro h; cases h))).trans hs)
    (by exact (hread (globals T 10) ((fullHeader_injective T).ne (by intro h; cases h))).trans hwidth)
    (by simp [M])
    (by
      intro slot
      have hne : fullHeader T (.publication (Fin.castAdd 4 slot)) ≠ fullHeader T (.publication 3) := by
        apply (fullHeader_injective T).ne
        fin_cases slot <;> decide
      rw [hread _ hne]
      fin_cases slot
      · exact hblank 0
      · exact hblank 1
      · exact hblank 2)
    (by
      intro i
      rw [hread _ (prefix_ne_routing (Fin.castAdd 175 (header T (.publication 3))) i).symm]
      exact hprivate i) depth
  refine ⟨v',(4*p+5)+n,hv.trans hu,by omega,?_⟩
  have hstock := hnarrow.final
  apply ExecWithin.seq (hnarrow.mono (by intro d z hz; omega))
  exact he.mono (by intro d z hz; dsimp only [M] at *; omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
