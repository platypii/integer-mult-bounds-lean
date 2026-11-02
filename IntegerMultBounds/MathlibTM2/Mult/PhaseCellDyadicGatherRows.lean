module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedGatherRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicRectangleSizing

/-! The actual padded gather word supplies both sides of an arbitrary dyadic
rectangle, without padding the core count to a replica-radix power. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem paddedGatherRows_dyadic {A s : ℕ} (a b width radius L w : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ 2^b)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^a) :
    ∃ rows : Fin (2^b) → Fin (2^a) → List GaussianInt,
    ∃ hlen : ∀ i j, (rows i j).length = L,
      (∀ i : Fin (coreGatherIndices s width radius L).length,
        (List.ofFn fun j => cstream A w (rows (paddedCoreIndex hcapacity i) j)).flatten =
          cstream A w (Fs.map (packedInterval
            (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten) ∧
      (let f := fun j i (k : Fin L) => (rows i j)[k.val]'(by rw [hlen]; exact k.isLt)
       cstream A w (paddedCoreGatherPayload (2^b) width radius L Fs) = cstream A w (replicaKeyWords f) ∧
       cstream A w (keyReplicaWords f) =
         (List.ofFn fun i => (List.ofFn fun j => cstream A w (rows i j)).flatten).flatten) := by
  let rows : Fin (2^b) → Fin (2^a) → List GaussianInt := fun i j =>
    paddedGatherRows (2^b) width radius L hcapacity Fs i (Fin.cast hreplicas.symm j)
  have hlen : ∀ i j, (rows i j).length = L := by
    intro i j
    exact paddedGatherRows_length _ _ _ _ _ _ _ _
  refine ⟨rows,hlen,?_,?_,?_⟩
  · intro i
    have h := paddedGatherRows_supplier (A := A) (2^b) width radius L w hcapacity Fs i
    have hc := List.ofFn_congr hreplicas (fun j : Fin Fs.length => cstream A w
      (paddedGatherRows (2^b) width radius L hcapacity Fs (paddedCoreIndex hcapacity i) j))
    rw [hc] at h
    exact h
  · have hinput := paddedGatherRows_source (A := A) (2^b) width radius L w hcapacity Fs
    have hc := List.ofFn_congr hreplicas (fun j : Fin Fs.length => cstream A w
      (List.ofFn fun i => paddedGatherRows (2^b) width radius L hcapacity Fs i j).flatten)
    rw [hc] at hinput
    exact hinput.trans (routedArchiveRows_cstream w rows hlen).symm
  · exact archiveRows_cstream w rows hlen

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
