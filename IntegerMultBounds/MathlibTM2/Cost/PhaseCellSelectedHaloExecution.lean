module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedHaloGeometry

/-! The manuscript halo execution instantiated on the actual selected target box. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.SelectedHaloGeometry
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  Routing Routing.RetainedHaloTensor Routing.RetainedTensorEnumeration Routing.HaloAxisSchedule
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

theorem run_exec {n : ℕ} (h : Sizes.Big n)
    (hroom : 2*Nat.clog 2 (Sizes.p n^8) ≤ Sizes.ℓ n-1)
    (axes : List (Fin (Sizes.d n))) (hn : axes.Nodup) (hall : ∀ i, i ∈ axes)
    (w : ℕ) (hw : 0 < w) (hp : 32 ≤ Sizes.p n)
    (cW : ℕ) (hcW : cW ≤ Sizes.p n) (hwWidth : w ≤ cW*Sizes.p n)
    (f : (Fin (Sizes.d n) → ℕ) → GaussianInt) (hA : 4 ≤ A) (tail metadataTail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = HaloMetadataFit.metadataWidth (Sizes.T n) w axes.length)
    (hz : S.R 116 = []) (hf : HaloPassContext.Fresh S)
    (hb : ∀ j ∈ HaloMetadataAxis.blank, S.R j = []) (hc : S.R 81 = [])
    (hq : S.R 72 = binSyms (HaloMetadataFit.metadataWidth (Sizes.T n) w axes.length) axes.length++
      metadata A (axis n) ∅ (ManuscriptHaloAxes.stages (axis n) axes hn hall (Sizes.p n) w hw hp
        (by simpa only [Fintype.card_fin] using dimension_le h) (fun _ => rfl) (fun _ => rfl))++metadataTail)
    (hsrc : S.R 39 = RetainedTensorEnumeration.stream (axis n) ∅ axes f (csyms A w)++tail) :
    ∃ vf, ∃ m : ℕ, vf.user = v.user ∧ (m : ℝ) ≤
      245*(Sizes.T n*w : ℕ)+
        (axes.length : ℝ)*(4577790*(cW : ℝ)*(Sizes.T n : ℝ)*
          (Sizes.p n : ℝ)^(129/128 : ℝ)+3)+2 ∧
      Exec body PreparedHaloAxes.run (mk v S) m
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream (axis n) Finset.univ axes f (csyms A w)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        18056*(Sizes.T n*w)) depth PreparedHaloAxes.run (mk v S) m
        (mk vf {S with R := (Function.update (Function.update S.R 72 metadataTail)
          39 (RetainedTensorEnumeration.stream (axis n) Finset.univ axes f (csyms A w)++tail))})) := by
  have hvolume := volume_eq h hroom
  have hbytes : volume (axis n) ∅*w ≤ 2^(Sizes.p n^2-4) := by
    rw [hvolume]
    apply bytes_le h (by omega) w
    exact hwWidth.trans (by simpa only [pow_two] using Nat.mul_le_mul_right (Sizes.p n) hcW)
  have hex := ManuscriptHaloAxes.run_exec (body := body) (axis n) axes hn hall
    (Sizes.p n) w hw hp (by simpa only [Fintype.card_fin] using dimension_le h) (fun _ => rfl) (fun _ => rfl)
    (coarse_room hroom) hbytes cW hwWidth f hA tail metadataTail v S
    (by simpa only [hvolume] using hV) hz hf hb hc
    (by simpa only [hvolume] using hq) hsrc
  simpa only [hvolume] using hex

end IntegerMultBounds.MathlibTM2.Cost.SelectedHaloGeometry
