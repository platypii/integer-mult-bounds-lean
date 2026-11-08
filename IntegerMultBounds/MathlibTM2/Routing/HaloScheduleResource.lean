module

public import IntegerMultBounds.MathlibTM2.Routing.HaloStageResource
public import IntegerMultBounds.MathlibTM2.Routing.PreparedHaloAxes

/-! Concrete global stage budgets discharge the runtime loop's cost premises.
Polynomial metadata/setup units are absorbed by the manuscript's large core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloScheduleResource
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz HaloPassContext RetainedHaloTensor RetainedTensorEnumeration
  HaloAxisSchedule HaloStageResource
variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

theorem amortized_le (T L w U : ℕ) (hU : U ≤ L) : ((2*T)/L*w)*U ≤ 2*(T*w) := by
  have hd : (2*T)/L*L ≤ 2*T := Nat.div_mul_le_self _ _
  calc
    _ ≤ ((2*T)/L*w)*L := Nat.mul_le_mul_left _ hU
    _ = ((2*T)/L*L)*w := by ring
    _ ≤ (2*T)*w := Nat.mul_le_mul_right w hd
    _ = _ := by ring

theorem stage_budgets (axis : ι → Axis) (axes : List ι) (hn : axes.Nodup) (hall : ∀ i, i ∈ axes)
    (stages : List (Stage ι)) (w V L H K : ℕ)
    (hL : ∀ i, (axis i).L = L) (hH : ∀ i, (axis i).H = H) (hLpos : 0 < L)
    (hlarge : 64*Fintype.card ι*H ≤ L)
    (horder : ∀ s ∈ stages, s.left++s.i::s.right = axes)
    (hparams : ∀ s ∈ stages, s.params.w = w ∧ s.params.V = V)
    (hready : ∀ done s todo, stages = done++s::todo → Ready axis (after ∅ done) s)
    (hsizing : ∀ s ∈ stages, s.params.L ≤ s.params.N ∧
      2^s.params.k ≤ 2*s.params.L ∧ 2^s.params.r ≤ 2*(s.params.L+2*s.params.H) ∧ s.params.k ≤ K ∧ s.params.r ≤ K)
    (htime : timeUnit K K V (2*axes.length) ≤ L) (hstock : stockUnit V (2*axes.length) ≤ L) :
    ∀ done s todo, stages = done++s::todo →
      time axis (after ∅ done) s ≤ (volume axis ∅*w)*(992*K+6654) ∧
      HaloAxisSchedule.reserve axis (after ∅ done) s ≤ 17320*(volume axis ∅*w) := by
  intro done s todo hd
  have hs : s ∈ stages := by rw [hd]; simp
  rcases hsizing s hs with ⟨hcoarse,hk,hr,hkmax,hrmax⟩
  have hh := stage_bills_le axis (after ∅ done) s
    (by rw [horder s hs]; exact hn) (by intro i; rw [horder s hs]; exact hall i)
    (hready done s todo hd) L H hL hH hLpos hlarge hcoarse hk hr
  rw [(hparams s hs).1,(hparams s hs).2,horder s hs] at hh
  have hu : timeUnit s.params.k s.params.r V (2*axes.length) ≤ L := by
    apply le_trans _ htime
    dsimp only [timeUnit]
    omega
  have ha := amortized_le (volume axis ∅) L w _ hu
  have hb := amortized_le (volume axis ∅) L w _ hstock
  have hc := Nat.mul_le_mul_left (volume axis ∅*w)
    (show 496*s.params.k+496*s.params.r+6652 ≤ 992*K+6652 by omega)
  constructor
  · nlinarith only [hh.1,ha,hc]
  · nlinarith only [hh.2,hb]

theorem run_exec (axis : ι → Axis) (axes : List ι) (hn : axes.Nodup) (hall : ∀ i, i ∈ axes)
    (stages : List (Stage ι)) (w V L H K : ℕ)
    (hL : ∀ i, (axis i).L = L) (hH : ∀ i, (axis i).H = H) (hLpos : 0 < L)
    (hlarge : 64*Fintype.card ι*H ≤ L)
    (horder : ∀ s ∈ stages, s.left++s.i::s.right = axes)
    (hparams : ∀ s ∈ stages, s.params.w = w ∧ s.params.V = V)
    (hready : ∀ done s todo, stages = done++s::todo → Ready axis (after ∅ done) s)
    (hsizing : ∀ s ∈ stages, s.params.L ≤ s.params.N ∧
      2^s.params.k ≤ 2*s.params.L ∧ 2^s.params.r ≤ 2*(s.params.L+2*s.params.H) ∧ s.params.k ≤ K ∧ s.params.r ≤ K)
    (htime : timeUnit K K V (2*axes.length) ≤ L) (hstock : stockUnit V (2*axes.length) ≤ L)
    (hfit : stages.length < 2^V) (f : (ι → ℕ) → GaussianInt) (hA : 4 ≤ A)
    (tail metadataTail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hz : S.R 116 = []) (hf : Fresh S)
    (hb : ∀ j ∈ HaloMetadataAxis.blank, S.R j = []) (hc : S.R 81 = [])
    (hq : S.R 72 = binSyms V stages.length++metadata A axis ∅ stages++metadataTail)
    (hsrc : S.R 39 = RetainedTensorEnumeration.stream axis ∅ axes f (csyms A w)++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ readUnaryDimensionCost V stages.length+
        stages.length*((volume axis ∅*w)*(992*K+6654)+3)+2 ∧
      Exec body PreparedHaloAxes.run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream axis (after ∅ stages) axes f (csyms A w)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (3*readUnaryDimensionCost V stages.length+17321*(volume axis ∅*w))) depth PreparedHaloAxes.run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream axis (after ∅ stages) axes f (csyms A w)++tail))})) := by
  obtain ⟨vf,n,hu,hn',he,hs⟩ := PreparedHaloAxes.run_exec (body := body) axis axes hn hall stages w V L H
    ((volume axis ∅*w)*(992*K+6654)) (17320*(volume axis ∅*w)) hL hH hLpos hlarge horder hparams hready
    (stage_budgets axis axes hn hall stages w V L H K hL hH hLpos hlarge horder hparams hready hsizing htime hstock)
    hfit f hA tail metadataTail v S hV hz hf hb hc hq hsrc
  refine ⟨vf,n,hu,hn',he,?_⟩
  intro depth
  exact (hs depth).mono (by intro d z hh; omega)

end IntegerMultBounds.MathlibTM2.Routing.HaloScheduleResource
