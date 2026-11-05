module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGeneratedBoundarySolve

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
  ScalarPlacement ScalarPlacement.FullLineInputPlan ScalarPlacement.ComputedClassBanks CommonClassGeometry PackedTranspose
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U}
noncomputable section

/-- Prepare the narrow ruler, generate all controls, solve once and archive
the boundary crops, retaining the generated headers for publication. -/
def callerPreparedBoundarySolve (src : Fin 11 → Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (widthSource : Fin (T+solverRegisterCount)) (recovery : Bool) :
    Pr P (MachineTapes (T+solverRegisterCount)) Q A U :=
  .seq (seamNarrowWidthProgram (solverSource (src 0)))
    (callerGeneratedBoundarySolve src hR hQ widthSource recovery)

theorem callerPreparedBoundarySolve_exec (src : Fin 11 → Fin T) (hsrc : src 8 ≠ src 4)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (widthSource : Fin (T+solverRegisterCount))
    (D coreWidth : ℕ) (hw : 0 < coreWidth) (hroom : 3*coreWidth < s) (recovery : Bool) (hA : 96 ≤ A)
    {p u l target t : ℕ} [NeZero t] {d : ℝ}
    (hp : 4 ≤ p) (hst : s < t) (hu : 1 ≤ u) (hwidth : 8*p ≤ 2^u)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : (u : ℝ)*d ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) (htarget : p+2 ≤ target)
    (Fs : List (ZMod s → GaussianInt)) (hFs : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (X F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (u : ℝ)) = 1)
    (W radius : ℕ) (v : HS (MachineTapes (T+solverRegisterCount)) Q A U)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hraw : ∀ i, (S.R (unarySource _ (solverSource (src i)))).length =
      globalValues p u l target s t (inverseCallerWordWidth p u l target s t) W Fs.length radius coreWidth i)
    (hzero : S.R (fullHeader _ .zero) = [])
    (hblank : ∀ r : SolverRole, S.R (solverRegister T r) = [])
    (hleft : ∀ r : SolverRole, S.L (solverRegister T r) = [])
    (hambient : S.R (fullHeader _ .input) =
      cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten)
    (hblankNarrow : S.R (fullHeader _ (.publication 3)) = [])
    (hprivate : ∀ i : Fin tapeCount, S.R (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i) = [])
    (hvolumeFit : s*(2*p+13) < 2^D)
    (hD : (S.R (unarySource _ widthSource)).length = D)
    (hlineBinary : S.R (globals _ 4) = binSyms D s)
    (hwidthBinary : S.R (globals _ 10) = binSyms D coreWidth)
    (hskip : ∀ j : Fin 2, S.R (fullHeader _ (.publication ⟨4+j.val,by omega⟩)) = [])
    (hcounts : ∀ slot : Fin 3, S.R (fullHeader _ (.publication (Fin.castAdd 4 slot))) = [])
    (C : ℕ) (hpush : mnProgPush ((callerFullLineProducer T Q hR hQ).gridProgram (P := P) (U := U) (A := A) recovery) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) (depth : ℕ) :
    let B := inverseCallerWordWidth p u l target s t
    let M : Stacks (MachineTapes (T+solverRegisterCount)) A :=
      {S with R := Function.update S.R (fullHeader _ (.publication 3)) (List.replicate (2*p+13) tick)}
    let F := callerBoundaryGeometryState widthSource s coreWidth (2*p+13) M
    let producer := callerFullLineProducer T Q hR hQ
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607))
    let solveStock := setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r)
    let volume := r.inputs.length*s*(2*p+13)
    let generateTime := ((2*p+13)*(4*D+10)+4*D+8)+boundaryCountExportCost D s coreWidth (2*p+13)+(2*D+2)
    let generateStock := 2*(4*D+4)+3*boundaryCountExportCost D s coreWidth (2*p+13)
    ∃ v' n output, ∃ banks : List (List (List GaussianInt)),
      v'.user = v.user ∧ n ≤ (4*p+5)+(generateTime+((4*B+5)+((solveTime+(242*volume+45))+(2*B+3)))) ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      List.Forall₂ (SeamCropRows p coreWidth r (fun _ => J)) (boundaryCropSchedule s coreWidth).reverse banks ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (13*(4*p+5)+(generateStock+(2*(4*B+5)+(solveStock+(480*volume+86)))))) depth
        (callerPreparedBoundarySolve src hR hQ widthSource recovery) (mk v S) n
        (mk v' {F with R := (Function.update F.R (fullHeader (T+solverRegisterCount) (.publication 6))
          ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (fullHeader (T+solverRegisterCount) (.publication 6))))}) := by
  dsimp only
  let M : Stacks (MachineTapes (T+solverRegisterCount)) A :=
    {S with R := Function.update S.R (fullHeader _ (.publication 3)) (List.replicate (2*p+13) tick)}
  have hread (i : Fin (MachineTapes (T+solverRegisterCount)))
      (hi : i ≠ fullHeader _ (.publication 3)) : M.R i = S.R i := by
    dsimp only [M]
    exact Function.update_of_ne hi _ _
  have hsource (i : Fin (T+solverRegisterCount)) : M.R (unarySource _ i) = S.R (unarySource _ i) :=
    hread _ (fullHeader_ne_bank id (.publication 3) i).symm
  have hheader (r : Role) (hr : r ≠ .publication 3) : M.R (fullHeader _ r) = S.R (fullHeader _ r) :=
    hread _ ((fullHeader_injective _).ne hr)
  have hpub (i : Fin 7) (hi : i ≠ 3) : M.R (fullHeader _ (.publication i)) = S.R (fullHeader _ (.publication i)) :=
    hheader _ (fun he => hi (Role.publication.inj he))
  have hprivateM (i : Fin tapeCount) : M.R (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i) = [] :=
    (hread _ (prefix_ne_routing _ i).symm).trans (hprivate i)
  have hprecision : (S.R (unarySource _ (solverSource (src 0)))).length = p := by
    simpa [globalValues] using hraw 0
  obtain ⟨v₁,hu₁,he₁⟩ := seamNarrowWidth_exec_within body (solverSource (src 0)) p v S hprecision
    hblankNarrow (hprivate _) depth
  obtain ⟨v₂,n₂,output,banks,hu₂,hn₂,hproduced,hbanks,he₂⟩ := callerGeneratedBoundarySolve_exec
    src hsrc hR hQ widthSource D coreWidth hw hroom recovery hA hp hst hu hwidth hθ hgap hbudget hband hpad htarget
    Fs hFs X Y hX hY J hJ W radius v₁ M
    (by intro i; rw [hsource]; exact hraw i)
    ((hheader .zero (by simp)).trans hzero)
    (fun r => (hread _ (solverRegister_ne_header T r (.publication 3))).trans (hblank r))
    hleft ((hheader .input (by simp)).trans hambient)
    (by simp [M]) hprivateM hvolumeFit
    (by rw [hsource]; exact hD)
    ((hheader (.scalar 4) (by simp)).trans hlineBinary)
    ((hheader (.scalar 10) (by simp)).trans hwidthBinary)
    (by
      intro j
      rw [hpub _ (by intro he; have hv := congrArg Fin.val he; change 4+j.val = 3 at hv; omega)]
      exact hskip j)
    (by
      intro slot
      rw [hpub _ (by intro he; have hv := congrArg Fin.val he; change slot.val = 3 at hv; have := slot.isLt; omega)]
      exact hcounts slot)
    C hpush hbody depth
  have harc : M.R (fullHeader (T+solverRegisterCount) (.publication 6)) =
      S.R (fullHeader (T+solverRegisterCount) (.publication 6)) := hpub 6 (by decide)
  rw [harc] at he₂
  refine ⟨v₂,(4*p+5)+n₂,output,banks,hu₂.trans hu₁,Nat.add_le_add_left hn₂ _,hproduced,hbanks,?_⟩
  have hpoint := he₁.final
  apply ExecWithin.seq
  · exact he₁.mono (by intro d z hz; omega)
  · exact he₂.mono (by intro d z hz; dsimp only [M] at hpoint hz ⊢; omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
