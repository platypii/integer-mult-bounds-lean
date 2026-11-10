module

public import IntegerMultBounds.MathlibTM2.Routing.HaloTraversal
public import IntegerMultBounds.MathlibTM2.Routing.HaloManuscriptSizing
public import IntegerMultBounds.MathlibTM2.Cost.ManuscriptHaloTime

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

/-- The ordinary tensor archive already dominates its axis count. -/
theorem axisCount_le_bytes (axis : ι → Axis) (p w : ℕ)
    (hw : 0 < w) (hp : 32 ≤ p) (hd : Fintype.card ι ≤ p)
    (hL : ∀ i, (axis i).L = core p) :
    Fintype.card ι ≤ volume axis ∅*w := by
  by_cases hz : Fintype.card ι = 0
  · omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hz)
  have hfactor : (axis i).N*localLength axis ∅ i ≤ volume axis ∅ := by
    apply Finset.single_le_prod _ (Finset.mem_univ i)
    intro j _
    have hj := Nat.mul_pos (axis j).N_pos (axis j).L_pos
    simp only [localLength,Finset.notMem_empty,ite_false]
    omega
  have hcore : p ≤ core p :=
    (le_self_pow (by omega : 1 ≤ p) (by decide : (8 : ℕ) ≠ 0)).trans
      (core_bounds p (by omega)).1
  have hlocal : core p ≤ (axis i).N*localLength axis ∅ i := by
    simpa only [localLength,Finset.notMem_empty,ite_false,hL i] using
      Nat.le_mul_of_pos_left (core p) (axis i).N_pos
  exact hd.trans (hcore.trans (hlocal.trans (hfactor.trans
    (Nat.le_mul_of_pos_right _ hw))))

theorem run_exec (axis : ι → Axis) (axes : List ι) (hn : axes.Nodup) (hall : ∀ i, i ∈ axes)
    (p w : ℕ) (hw : 0 < w) (hp : 32 ≤ p) (hd : Fintype.card ι ≤ p)
    (hL : ∀ i, (axis i).L = core p) (hH : ∀ i, (axis i).H = halo p)
    (hcoarse : ∀ i, (axis i).L ≤ (axis i).N)
    (hbytes : volume axis ∅*w ≤ 2^(p^2-4))
    (cW : ℕ) (hwWidth : w ≤ cW*p)
    (f : (ι → ℕ) → GaussianInt) (hA : 4 ≤ A) (tail metadataTail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = HaloMetadataFit.metadataWidth (volume axis ∅) w axes.length)
    (hz : S.R 116 = []) (hf : HaloPassContext.Fresh S)
    (hb : ∀ j ∈ HaloMetadataAxis.blank, S.R j = []) (hc : S.R 81 = [])
    (hq : S.R 72 = binSyms (HaloMetadataFit.metadataWidth (volume axis ∅) w axes.length) axes.length++
      metadata A axis ∅ (stages axis axes hn hall p w hw hp hd hL hH)++metadataTail)
    (hsrc : S.R 39 = RetainedTensorEnumeration.stream axis ∅ axes f (csyms A w)++tail) :
    ∃ vf, ∃ n : ℕ, vf.user = v.user ∧ (n : ℝ) ≤
      245*(volume axis ∅*w : ℕ)+
        (axes.length : ℝ)*(4577790*(cW : ℝ)*(volume axis ∅ : ℝ)*
          (p : ℝ)^(129/128 : ℝ)+3)+2 ∧
      Exec body PreparedHaloAxes.run (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream axis Finset.univ axes f (csyms A w)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        18056*(volume axis ∅*w)) depth PreparedHaloAxes.run (mk v S) n
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
  have hcount : axes.length ≤ volume axis ∅*w := by
    rw [hcard]
    exact axisCount_le_bytes axis p w hw hp hd hL
  have hpos : 0 < volume axis ∅*w :=
    Nat.mul_pos (RetainedHaloVolume.volume_pos axis ∅) hw
  have hwidth : HaloMetadataFit.metadataWidth (volume axis ∅) w axes.length ≤ p^2 := by
    have hh := HaloMetadataFit.metadataWidth_le (volume axis ∅) w axes.length (p^2-4)
      hpos hcount hbytes
    have hroom : 4 ≤ p^2 := by nlinarith
    omega
  have hstartup := HaloMetadataFit.metadataStartup_le (volume axis ∅) w axes.length hpos hcount
  have hD : 2*axes.length ≤ p^2 := by rw [hcard]; nlinarith
  have hbudget := HaloManuscriptSizing.stage_budgets axis axes hn hall ss p w V hp hd hwidth hD
    hL hH horder hparams hready hsizing
  have hend : after ∅ ss = Finset.univ := after_all ss (by intro i; rw [hi]; exact hall i)
  obtain ⟨vf,n,hu,ht,he,hs⟩ := PreparedHaloAxes.run_exec (body := body) axis axes hn hall ss w V
    (core p) (halo p) ((volume axis ∅*w)*(992*Nat.clog 2 (core p+2*halo p)+6654)) (17320*(volume axis ∅*w))
    hL hH (Nat.two_pow_pos _) (halo_room p _ hp hd) horder hparams hready hbudget hfit
    f hA tail metadataTail v S hV hz hf hb hc (by simpa only [hlen] using hq) hsrc
  refine ⟨vf,n,hu,?_,?_,?_⟩
  · have ht' : n ≤ readUnaryDimensionCost V axes.length+
        axes.length*((volume axis ∅*w)*(992*Nat.clog 2 (core p+2*halo p)+6654)+3)+2 := by
      simpa only [hlen] using ht
    have hlocal : 992*Nat.clog 2 (core p+2*halo p)+6654 ≤
        8928*(Nat.log 2 p+1)+6654 := by
      have hh := Nat.mul_le_mul_left 992 (routingExponent_le p hp)
      omega
    have hstage := Nat.mul_le_mul_left (volume axis ∅*w) hlocal
    have hall := Nat.mul_le_mul_left axes.length (Nat.add_le_add_right hstage 3)
    have hsteps : n ≤ readUnaryDimensionCost V axes.length+
        axes.length*((volume axis ∅*w)*(8928*(Nat.log 2 p+1)+6654)+3)+2 :=
      ht'.trans (by omega)
    have hstepsR : (n : ℝ) ≤
        ((readUnaryDimensionCost V axes.length+
          axes.length*((volume axis ∅*w)*(8928*(Nat.log 2 p+1)+6654)+3)+2 : ℕ) : ℝ) := by
      exact_mod_cast hsteps
    have htime := hstepsR.trans (Cost.manuscriptHaloTime_le p w (volume axis ∅) axes.length
      (readUnaryDimensionCost V axes.length) cW (by omega) hwWidth)
    have hstartupR : (readUnaryDimensionCost V axes.length : ℝ) ≤
        245*(volume axis ∅*w : ℕ) := by exact_mod_cast hstartup
    linarith only [htime,hstartupR]
  · simpa only [hend] using he
  · intro depth
    have hh := hs depth
    rw [hend,hlen] at hh
    dsimp only [V] at hh
    exact hh.mono (by intro d z hz'; omega)

end IntegerMultBounds.MathlibTM2.Routing.ManuscriptHaloAxes
