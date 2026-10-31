module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedSupplierBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherRows

/-! Ordered movement classes use the existing mathematical supplier records.
Their own halo geometry determines the exact exposed payload and output bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s t : ℕ} [NeZero s] [NeZero t]
  {producer : PackedProducerPlan T Q} {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
namespace GeneratedSupplierCall

theorem payload_coreGather (c : GeneratedSupplierCall (A := A) producer t J)
    (width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (hwidth : c.job.coreWidth = width) (hradius : c.job.radius = radius)
    (hk : c.job.k ∈ coreGatherIndices s width radius L)
    (hword : c.job.W = w) (hFs : c.job.Fs = Fs) :
    c.payload = cstream A w (Fs.map (packedInterval (coreStart width c.job.k-radius) L)).flatten := by
  have hlength := (coreGatherIndices_spec s width radius L c.job.k hk).2.2
  have hhalo := c.job.haloLength
  rw [hwidth,hradius] at hhalo
  have hlen : c.job.b-c.job.a = L := hhalo.trans hlength
  have horigin := c.job.haEq
  rw [hwidth,hradius] at horigin
  unfold payload
  rw [hlen,horigin,hFs,hword]

theorem payload_length_coreGather (c : GeneratedSupplierCall (A := A) producer t J)
    (width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (hwidth : c.job.coreWidth = width) (hradius : c.job.radius = radius)
    (hk : c.job.k ∈ coreGatherIndices s width radius L)
    (hword : c.job.W = w) (hFs : c.job.Fs = Fs) :
    c.payload.length = Fs.length*L*w := by
  rw [c.payload_coreGather width radius L w Fs hwidth hradius hk hword hFs,length_cstream]
  obtain ⟨hl,hr,he⟩ := coreGatherIndices_spec s width radius L c.job.k hk
  have hfit : coreStart width c.job.k-radius+L ≤ s := by omega
  simp [List.length_flatten,List.map_map,Function.comp_def,packedInterval_length _ hfit]

theorem volume_coreGather (c : GeneratedSupplierCall (A := A) producer t J)
    (width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (hwidth : c.job.coreWidth = width) (hk : c.job.k ∈ coreGatherIndices s width radius L)
    (hword : c.job.W = w) (hFs : c.job.Fs = Fs) :
    c.volume = Fs.length*(L-2*radius)*w := by
  have hlength := (coreGatherIndices_spec s width radius L c.job.k hk).2.2
  have hcore : coreLength s width c.job.k = L-2*radius := by omega
  simp only [volume,hFs,hword,hwidth,hcore]
end GeneratedSupplierCall

/-- A list of indexed calls has exactly the real stream returned by exposure. -/
theorem coreSupplierCalls_payload (width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (calls : Fin (coreGatherIndices s width radius L).length → GeneratedSupplierCall (A := A) producer t J)
    (hwidth : ∀ i, (calls i).job.coreWidth = width) (hradius : ∀ i, (calls i).job.radius = radius)
    (hk : ∀ i, (calls i).job.k = (coreGatherIndices s width radius L)[i.val])
    (hword : ∀ i, (calls i).job.W = w) (hFs : ∀ i, (calls i).job.Fs = Fs) :
    (List.ofFn calls).flatMap GeneratedSupplierCall.payload =
      (List.ofFn fun i : Fin (coreGatherIndices s width radius L).length =>
        cstream A w (Fs.map (packedInterval
          (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten).flatten := by
  have hp (i : Fin (coreGatherIndices s width radius L).length) :=
    (calls i).payload_coreGather width radius L w Fs (hwidth i) (hradius i)
      (by rw [hk i]; exact List.getElem_mem i.isLt) (hword i) (hFs i)
  simp only [List.flatMap_def,List.map_ofFn,Function.comp_def]
  congr 1
  congr 1
  funext i
  simpa only [hk i] using hp i

/-- Uniform core lengths give the retained output volume without per-job sums. -/
theorem coreSupplierCalls_volume (width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (calls : Fin (coreGatherIndices s width radius L).length → GeneratedSupplierCall (A := A) producer t J)
    (hwidth : ∀ i, (calls i).job.coreWidth = width)
    (hk : ∀ i, (calls i).job.k = (coreGatherIndices s width radius L)[i.val])
    (hword : ∀ i, (calls i).job.W = w) (hFs : ∀ i, (calls i).job.Fs = Fs) :
    ((List.ofFn calls).map GeneratedSupplierCall.volume).sum =
      (coreGatherIndices s width radius L).length*(Fs.length*(L-2*radius)*w) := by
  have hv (i : Fin (coreGatherIndices s width radius L).length) :=
    (calls i).volume_coreGather width radius L w Fs (hwidth i)
      (by rw [hk i]; exact List.getElem_mem i.isLt) (hword i) (hFs i)
  simp only [List.map_ofFn,Function.comp_def,hv,List.ofFn_const,List.sum_replicate,smul_eq_mul]
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
