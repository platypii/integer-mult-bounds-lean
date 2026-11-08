module

public import IntegerMultBounds.MathlibTM2.Routing.HaloTraversal
public import IntegerMultBounds.MathlibTM2.Routing.HaloManuscriptSizing

/-! Execute all manuscript target halos from axis dimensions. Stage parameters,
metadata fit, freshness and budgets are derived internally. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.ManuscriptHaloAxes
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  RetainedHaloTensor RetainedTensorEnumeration HaloAxisSchedule HaloManuscriptSizing
variable {ι : Type} [DecidableEq ι] [Fintype ι]

omit [DecidableEq ι] [Fintype ι] in
theorem gap (axis : ι → Axis) (p : ℕ) (hp : 32 ≤ p)
    (hL : ∀ i, (axis i).L = core p) (hH : ∀ i, (axis i).H = halo p) :
    ∀ i, 2*(axis i).H ≤ (axis i).L := by
  intro i
  rw [hL,hH]
  have hh := halo_room p 1 hp (by omega)
  omega

theorem volumes (axis : ι → Axis) (p : ℕ) (hp : 32 ≤ p) (hd : Fintype.card ι ≤ p)
    (hL : ∀ i, (axis i).L = core p) (hH : ∀ i, (axis i).H = halo p) :
    ∀ retained, volume axis retained ≤ 2*volume axis ∅ := by
  intro retained
  exact (RetainedHaloVolume.volume_lt_two_of_large_core axis retained (core p) (halo p)
    hL hH (Nat.two_pow_pos _) (halo_room p _ hp hd)).le

def stages (axis : ι → Axis) (axes : List ι) (hn : axes.Nodup) (hall : ∀ i, i ∈ axes)
    (p w : ℕ) (hw : 0 < w) (hp : 32 ≤ p) (hd : Fintype.card ι ≤ p)
    (hL : ∀ i, (axis i).L = core p) (hH : ∀ i, (axis i).H = halo p) : List (Stage ι) :=
  HaloTraversal.build axis w hw (gap axis p hp hL hH) (volumes axis p hp hd hL hH)
    [] axes (by simpa using hn) (by simpa using hall)

variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

theorem run_exec (axis : ι → Axis) (axes : List ι) (hn : axes.Nodup) (hall : ∀ i, i ∈ axes)
    (p w : ℕ) (hw : 0 < w) (hp : 32 ≤ p) (hd : Fintype.card ι ≤ p)
    (hL : ∀ i, (axis i).L = core p) (hH : ∀ i, (axis i).H = halo p)
    (hcoarse : ∀ i, (axis i).L ≤ (axis i).N)
    (hwidth : HaloMetadataFit.metadataWidth (volume axis ∅) w axes.length ≤ p^2)
    (f : (ι → ℕ) → GaussianInt) (hA : 4 ≤ A) (tail metadataTail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = HaloMetadataFit.metadataWidth (volume axis ∅) w axes.length)
    (hz : S.R 116 = []) (hf : HaloPassContext.Fresh S)
    (hb : ∀ j ∈ HaloMetadataAxis.blank, S.R j = []) (hc : S.R 81 = [])
    (hq : S.R 72 = binSyms (HaloMetadataFit.metadataWidth (volume axis ∅) w axes.length) axes.length++
      metadata A axis ∅ (stages axis axes hn hall p w hw hp hd hL hH)++metadataTail)
    (hsrc : S.R 39 = RetainedTensorEnumeration.stream axis ∅ axes f (csyms A w)++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤
      readUnaryDimensionCost (HaloMetadataFit.metadataWidth (volume axis ∅) w axes.length) axes.length+
        axes.length*((volume axis ∅*w)*(992*Nat.clog 2 (core p+2*halo p)+6654)+3)+2 ∧
      Exec body PreparedHaloAxes.run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream axis Finset.univ axes f (csyms A w)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*readUnaryDimensionCost (HaloMetadataFit.metadataWidth (volume axis ∅) w axes.length) axes.length+
          17321*(volume axis ∅*w))) depth PreparedHaloAxes.run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream axis Finset.univ axes f (csyms A w)++tail))})) := by
  let ss := stages axis axes hn hall p w hw hp hd hL hH
  let V := HaloMetadataFit.metadataWidth (volume axis ∅) w axes.length
  have hi : ss.map Stage.i = axes := HaloTraversal.build_indices axis w hw _ _ [] axes _ _
  have hlen : ss.length = axes.length := by rw [←hi,List.length_map]
  have horder : ∀ s ∈ ss, s.left++s.i::s.right = axes :=
    HaloTraversal.build_order axis w hw _ _ [] axes _ _
  have hparams : ∀ s ∈ ss, s.params.w = w ∧ s.params.V = V :=
    HaloTraversal.build_params axis w hw _ _ [] axes _ _
  have hready : ∀ done s todo, ss = done++s::todo → Ready axis (after ∅ done) s :=
    HaloTraversal.build_ready axis w hw _ _ [] axes _ _
  have hsizing := HaloTraversal.build_sizing axis w hw (gap axis p hp hL hH)
    (volumes axis p hp hd hL hH) hcoarse [] axes (by simpa using hn) (by simpa using hall)
  have hfit : ss.length < 2^V := by
    have hh : 8*volume axis ∅*w+2*axes.length+1 ≤ 2^V := Nat.le_pow_clog (by decide) _
    omega
  have hu : axes.toFinset = Finset.univ := by ext i; simp [hall i]
  have hcard : axes.length = Fintype.card ι := by
    rw [←List.toFinset_card_of_nodup hn,hu,Finset.card_univ]
  have hD : 2*axes.length ≤ p^2 := by rw [hcard]; nlinarith
  have hbudget := HaloManuscriptSizing.stage_budgets axis axes hn hall ss p w V hp hd hwidth hD
    hL hH horder hparams hready hsizing
  have hend : after ∅ ss = Finset.univ := after_all ss (by intro i; rw [hi]; exact hall i)
  obtain ⟨vf,n,hu,ht,he,hs⟩ := PreparedHaloAxes.run_exec (body := body) axis axes hn hall ss w V
    (core p) (halo p) ((volume axis ∅*w)*(992*Nat.clog 2 (core p+2*halo p)+6654)) (17320*(volume axis ∅*w))
    hL hH (Nat.two_pow_pos _) (halo_room p _ hp hd) horder hparams hready hbudget hfit
    f hA tail metadataTail v S hV hz hf hb hc (by simpa only [hlen] using hq) hsrc
  refine ⟨vf,n,hu,?_,?_,?_⟩
  · simpa only [hlen] using ht
  · simpa only [hend] using he
  · intro depth
    have hh := hs depth
    rw [hend,hlen] at hh
    dsimp only [V] at hh
    exact hh.mono (by intro d z hz'; omega)

end IntegerMultBounds.MathlibTM2.Routing.ManuscriptHaloAxes
