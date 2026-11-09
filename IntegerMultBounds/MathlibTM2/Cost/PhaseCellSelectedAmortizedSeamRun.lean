module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPlacedSeamRun
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatherSchedule
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

theorem selectedAmortizedSeamProgram_exec (ct : ℕ) :
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
    let ks := coreSetupGroup s coreWidth (PhaseCellBand.width p u) (localityDepth p target) (0,s)
    u ≤ p → target ≤ ct*p →
    ∀ (hu : 1 ≤ u) (hwidth : 8*p ≤ 2^u)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
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
    (v : HS T' Q A U) (S : Stacks T' A)
    (ready : SeamReady input producer crops p u l target t coreWidth Fs ks (embStk e S))
    (depth : ℕ),
    let C := closedGridPush (U := U) (A := A) producer recovery
    let r := fullLineGridRecord (A := A) p u l target t Fs
    ∃ v' : HS T' Q A U, ∃ n : ℕ, ∃ output : List (Fin (A+4)), ∃ rss : List (List (List GaussianInt)),
      v'.user = v.user ∧ (n : ℝ) ≤ 2624001*(Sizes.T m : ℝ)+
        (Fs.length : ℝ)*D*(t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+
        726*(Fs.length*s*p : ℕ)+455 ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      List.Forall₂ (fun k rows => ExactCoreRows (A := A) p (2*p+13) coreWidth k Fs.reverse J rows) ks.reverse rss ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)*(Fs.length*s*p)+2*(C+1)*Sizes.T m+86)) depth
        (placedSeamProgram e input producer crops recovery ks) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (e crops.dst)
          ((rss.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++(embStk e S).R crops.dst))}) := by
  dsimp only
  obtain ⟨D,hD,hseam⟩ := selectedPlacedSeamProgram_exec (T := T) (T' := T') (Q := Q) (A := A)
    (U := U) (body := body) ct
  refine ⟨D,hD,?_⟩
  filter_upwards [hseam,selectedAmortizedGatherSchedule ct] with m hseam hschedule
  intro h i _ e he input producer hcompat crops recovery hA u target d huUpper htargetUpper
    hu hwidth hgap hbudget hband hpad htarget Fs hFs X Y hX hY J hJ
    v S ready depth
  let coreWidth := amortizedCoreWidth ct (Sizes.p m)
  let ks := coreSetupGroup (Sizes.s m i) coreWidth (PhaseCellBand.width (Sizes.p m) u)
    (localityDepth (Sizes.p m) target) (0,Sizes.s m i)
  have hcount : ks.length ≤ 3 := (hschedule h i u target htargetUpper).2.2.2.2.2.1
  have hstart (k : ℕ) (hk : k ∈ ks) : coreStart coreWidth k ≤ Sizes.s m i := by
    have hmem := (mem_coreSetupGroup _ _ _ _ _ _).mp hk
    exact (coreStart_lt_of_mem hmem.1).le
  obtain ⟨v',n,output,rss,huser,htime,hproduced,hrows,hwithin⟩ := hseam h i e he input producer hcompat crops coreWidth ks recovery hA u target d huUpper htargetUpper
    hu hwidth hgap hbudget hband hpad htarget Fs hFs X Y hX hY J hJ
    v S ready.input ready.bank ready.left ready.controls ready.crops hstart hcount ready.result depth
  refine ⟨v',n,output,rss,huser,htime,hproduced,?_,hwithin⟩
  exact hrows.imp (by intro k rows hr; exact SeamCropRows.exact_rows_native _ _ _ _ _ _ hr)

end IntegerMultBounds.MathlibTM2.Cost
