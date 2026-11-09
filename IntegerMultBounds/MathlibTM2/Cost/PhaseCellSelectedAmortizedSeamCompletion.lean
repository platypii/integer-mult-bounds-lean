module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedSeamRun
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedBoundaryArchivePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPublicationClass
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatherSchedule
public import IntegerMultBounds.NLogN.PhaseCellBoundaryCropSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamExactCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineSeamReady

/-! Generate ordinary full-line input, solve once, archive all seam crops and
retire the full-line result. Only the crop archive differs from the baseline. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement FullLineInputPlan
open Filter IntegerMultBounds.MathlibTM2.Mult
variable {T T' Q A : ℕ} {P U : Type} {body : P → Pr P T' Q A U}

theorem selectedAmortizedSeamCompletion_exec (ct cDB : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    ∀ (e : Fin T → Fin T') (he : Function.Injective e) (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
    (hcompat : input.Compatible producer)
    (crops : SeamCropPlan T producer.result) (recovery : Bool) (hA : 96 ≤ A)
    , let p := Sizes.p m
    let s := Sizes.s m i
    let t := Sizes.t m i
    let l := haloInverseRingLog s t
    ∀ (u target : ℕ) (d : ℝ),
    let coreWidth := amortizedCoreWidth ct p
    let ks := boundaryCropSchedule s coreWidth
    u ≤ p → target ≤ ct*p →
    ∀ (hu : 1 ≤ u) (hwidth : 8*p ≤ 2^u)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : (u : ℝ)*d ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) (htarget : p+2 ≤ target)
    (Fs : List (ZMod s → GaussianInt)) (hFs : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) (hFsPos : 1 ≤ Fs.length)
    (X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (X F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (u : ℝ)) = 1)
    (v : HS T' Q A U) (S : Stacks T' A)
    (ready : SeamReady input producer crops p u l target t coreWidth Fs ks (embStk e S))
    (W : ℕ) (hW : 2*p+13 ≤ W)
    (be : Fin 117 → Fin T') (hbe : Function.Injective be)
    (hsourcePort : be 95 = e crops.dst) (DB : ℕ) (hvolumeFit : s*W < 2^DB) (hDB : DB ≤ cDB*p)
    (masters : Fin 11 → Fin 117)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,coreWidth,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^DB)
    (boundaryInput : BoundaryHeaderSource (s := s) p coreWidth W DB Fs.length masters seedValue (embStk be S))
    (ambient : List (List (Fin (A+4)))) (outputTail : List (Fin (A+4)))
    (hdst : S.R (be 96) = ambient.flatten++outputTail)
    (hgood : (gatherPublicationClass s coreWidth (localityDepth p target*PhaseCellBand.width p u)
      (coreWidth+2*(localityDepth p target*PhaseCellBand.width p u))).BankAccurate p W
      (inversePublicationTargets p Fs J) ambient (3/(2:ℝ)^p))
    (depth : ℕ),
    let C := closedGridPush (U := U) (A := A) producer recovery
    let boundaryBill := boundaryHeaderTrafficFactor cDB*(Fs.length*(s*W))+(3*boundarySeamCost Fs.length (2*p+13) DB s coreWidth W+1)
    ∃ lines : List (List (Fin (A+4))), ∃ v' : HS T' Q A U, ∃ steps : ℕ,
      v'.user = v.user ∧ (steps : ℝ) ≤ 2624001*(Sizes.T m : ℝ)+
        (Fs.length : ℝ)*D*(t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+
        726*(Fs.length*s*p : ℕ)+455+(boundaryBill : ℕ) ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (inversePublicationTargets p Fs J) lines ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)*(Fs.length*s*p)+2*(C+1)*Sizes.T m+86)+
          (boundaryHeaderTrafficFactor cDB*(Fs.length*(s*W))+13*boundarySeamCost Fs.length (2*p+13) DB s coreWidth W))) depth
        (.seq (placedSeamProgram e input producer crops recovery ks)
          (preparedBoundaryArchivePublication be masters))
        (Host.mk v S) steps (Host.mk v' {S with R := (Function.update S.R (be 96) (lines.flatten++outputTail))}) := by
  dsimp only
  obtain ⟨D,hD,hseam⟩ := selectedAmortizedSeamProgram_exec (T := T) (T' := T')
    (Q := Q) (A := A) (U := U) (body := body) ct
  refine ⟨D,hD,?_⟩
  filter_upwards [hseam,selectedAmortizedCoreGeometry ct] with m hseam hgeometry
  intro h i _ e he input producer hcompat crops recovery hA u target d huUpper htargetUpper
    hu hwidth hgap hbudget hband hpad htarget Fs hFs hFsPos X Y hX hY J hJ v S ready
    W hW be hbe hsourcePort DB hvolumeFit hDB masters seedValue hvalues hfit boundaryInput
    ambient outputTail hdst hgood depth
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let width := amortizedCoreWidth ct p
  let radius := localityDepth p target*PhaseCellBand.width p u
  let proper := gatherPublicationClass s width radius (width+2*radius)
  let r := fullLineGridRecord (A := A) p u l target t Fs
  obtain ⟨vm,n,output,banks,huser,htime,hproduced,hbanks,hwithin⟩ := hseam
    h i e he input producer hcompat crops recovery hA u target d huUpper htargetUpper
    hu hwidth hgap hbudget hband hpad htarget Fs hFs X Y hX hY J hJ v S ready depth
  let word := (banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten
  let M : Stacks T' A := {S with R := Function.update S.R (e crops.dst) (word++S.R (e crops.dst))}
  have hread (j : Fin 117) (hj : j ≠ 95) : (embStk be M).R j = (embStk be S).R j := by
    exact Function.update_of_ne (by rw [←hsourcePort]; exact hbe.ne hj) _ _
  have hready := boundaryInput.of_frame p width W DB Fs.length masters seedValue
    (embStk be S) (embStk be M) (by intro j hj _; exact hread j hj)
  obtain ⟨hw,hpRoom,hrw,hroom,_⟩ := hgeometry h i u target htargetUpper
  change 3*width+PhaseCellBand.width p u ≤ s at hroom
  have hbandPos := PhaseCellBand.width_pos p u
  have hp : 1 ≤ p := by have := h.thirteen_le_p; omega
  have hrad : 0 < localityDepth p target*PhaseCellBand.width p u := localityCoreWidth_pos hp u target
  have hps : p ≤ s := by
    have hpPower : p ≤ p^8 := by simpa only [pow_one] using pow_le_pow_right' hp (show 1 ≤ 8 by decide)
    change p^8 ≤ width at hpRoom
    omega
  obtain ⟨lines,v',nb,hu',htb,hall,heb⟩ := preparedBoundaryArchivePublication_exec body be hbe masters
    p width W DB cDB (by omega) hW hw (by omega) hvolumeFit hDB hps seedValue hvalues hfit
    r (by simpa only [r,fullLineGridRecord] using hFsPos) (fun _ => J) (PhaseCellBand.width p u) (localityDepth p target) hrad hrw proper rfl
    (S.R (be 95)) outputTail M hready depth vm banks hbanks ambient
    (by simpa only [r,fullLineGridRecord,seamPublicationTargets,inversePublicationTargets] using hgood)
    (by simp only [embStk,M,Function.comp_apply,hsourcePort,Function.update_self,word])
    (by rw [hread 96 (by decide)]; exact hdst)
  have htotal := execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ hwithin heb
  have hfinal : ({M with R := (Function.update (Function.update M.R (be 95) (S.R (be 95)))
      (be 96) (lines.flatten++outputTail))} : Stacks T' A) =
      {S with R := (Function.update S.R (be 96) (lines.flatten++outputTail))} := by
    simp only [M,←hsourcePort,Function.update_idem,Function.update_eq_self]
  rw [hfinal] at htotal
  refine ⟨lines,v',n+nb,hu'.trans huser,?_,?_,htotal⟩
  · have htbReal := Nat.cast_le (α := ℝ).mpr htb
    simp only [r,fullLineGridRecord,p,s,width] at htbReal
    rw [Nat.cast_add]
    linarith
  · simpa only [r,fullLineGridRecord,seamPublicationTargets,inversePublicationTargets] using hall

end IntegerMultBounds.MathlibTM2.Cost
