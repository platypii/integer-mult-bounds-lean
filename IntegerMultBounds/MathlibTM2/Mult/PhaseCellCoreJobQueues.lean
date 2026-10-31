module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierCoreStepStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherRows

/-! The mathematical core jobs consume exactly the origin order and real
supplier stream computed by movement-class exposure. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A s : ℕ} [NeZero s]

namespace PackedNormalizedJob

theorem inputPayload_coreGather (r : PackedNormalizedJob A s) (width radius L w : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (hwidth : r.coreWidth = width) (hradius : r.radius = radius)
    (hk : r.k ∈ coreGatherIndices s width radius L) (hword : r.W = w) (hFs : r.Fs = Fs) :
    r.inputPayload = cstream A w (Fs.map (packedInterval (coreStart width r.k-radius) L)).flatten := by
  have hlength := (coreGatherIndices_spec s width radius L r.k hk).2.2
  have hhalo := r.haloLength
  rw [hwidth,hradius] at hhalo
  have hlen : r.b-r.a = L := hhalo.trans hlength
  have horigin := r.haEq
  rw [hwidth,hradius] at horigin
  unfold inputPayload
  rw [hlen,horigin,hFs,hword]

end PackedNormalizedJob

/-- The job list's binary queue has exactly the generated class-origin order. -/
theorem coreJobs_origins (width radius L V : ℕ)
    (jobs : Fin (coreGatherIndices s width radius L).length → PackedNormalizedJob A s)
    (hwidth : ∀ i, (jobs i).coreWidth = width) (hradius : ∀ i, (jobs i).radius = radius)
    (hk : ∀ i, (jobs i).k = (coreGatherIndices s width radius L)[i.val]) :
    (List.ofFn jobs).flatMap (fun r => binSyms (A := A) V r.a) =
      (coreGatherIndices s width radius L).flatMap (fun k => binSyms V (coreStart width k-radius)) := by
  have ha (i : Fin (coreGatherIndices s width radius L).length) :
      (jobs i).a = coreStart width (coreGatherIndices s width radius L)[i.val]-radius := by
    simpa only [hwidth,hradius,hk] using (jobs i).haEq
  simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,ha]
  congr 1
  simpa only [List.map_ofFn,Function.comp_def,List.get_eq_getElem] using
    congrArg (List.map fun k => binSyms (A := A) V (coreStart width k-radius))
      (List.ofFn_get (coreGatherIndices s width radius L))

/-- These are precisely the contiguous batches returned by inverse archive routing. -/
theorem coreJobs_payloads (width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (jobs : Fin (coreGatherIndices s width radius L).length → PackedNormalizedJob A s)
    (hwidth : ∀ i, (jobs i).coreWidth = width) (hradius : ∀ i, (jobs i).radius = radius)
    (hk : ∀ i, (jobs i).k = (coreGatherIndices s width radius L)[i.val])
    (hword : ∀ i, (jobs i).W = w) (hFs : ∀ i, (jobs i).Fs = Fs) :
    (List.ofFn jobs).flatMap PackedNormalizedJob.inputPayload =
      (List.ofFn fun i : Fin (coreGatherIndices s width radius L).length =>
        (List.ofFn fun j => cstream A w (coreGatherRows width radius L Fs i j)).flatten).flatten := by
  have hp (i : Fin (coreGatherIndices s width radius L).length) :=
    (jobs i).inputPayload_coreGather width radius L w Fs (hwidth i) (hradius i)
      (by rw [hk i]; exact List.getElem_mem i.isLt) (hword i) (hFs i)
  simp only [List.flatMap_def,List.map_ofFn,Function.comp_def]
  congr 1
  congr 1
  funext i
  rw [hp,coreGatherRows_supplier,hk]

/-- One shared counter is sufficient for every job in a movement class. -/
theorem coreJobs_payload_length (width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (jobs : Fin (coreGatherIndices s width radius L).length → PackedNormalizedJob A s)
    (hwidth : ∀ i, (jobs i).coreWidth = width) (hradius : ∀ i, (jobs i).radius = radius)
    (hk : ∀ i, (jobs i).k = (coreGatherIndices s width radius L)[i.val])
    (hword : ∀ i, (jobs i).W = w) (hFs : ∀ i, (jobs i).Fs = Fs) :
    ∀ i, (jobs i).inputPayload.length = Fs.length*L*w := by
  intro i
  have hlength := (coreGatherIndices_spec s width radius L (jobs i).k (by
    rw [hk i]; exact List.getElem_mem i.isLt)).2.2
  have hhalo := (jobs i).haloLength
  rw [hwidth,hradius] at hhalo
  rw [PackedNormalizedJob.inputPayload_length,hFs,hword,hhalo.trans hlength]

/-- The supplier's per-replica output length is constant throughout the class. -/
theorem coreJobs_core_length (width radius L : ℕ)
    (jobs : Fin (coreGatherIndices s width radius L).length → PackedNormalizedJob A s)
    (hwidth : ∀ i, (jobs i).coreWidth = width)
    (hk : ∀ i, (jobs i).k = (coreGatherIndices s width radius L)[i.val]) :
    ∀ i, coreLength s (jobs i).coreWidth (jobs i).k = L-2*radius := by
  intro i
  have hlength := (coreGatherIndices_spec s width radius L _ (List.getElem_mem i.isLt)).2.2
  rw [hwidth,hk]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
