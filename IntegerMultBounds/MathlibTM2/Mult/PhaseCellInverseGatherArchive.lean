module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileInverseStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedGatherRows

/-! Route the actual padded gather archive into contiguous supplier batches.
The finite padded matrix is constructed from the RHS list, never supplied. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace ArchiveTilePlan
variable {t₀ T Q c d W K s : ℕ}

/-- Exact physical output and the supplier payload identities concern the same
returned archive. The RHS list records the gather's physical replica order. -/
theorem inverse_gather_exec_within {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K) (hW : 0 < W)
    (width radius L w : ℕ) (hpacket : W = L*w)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^d)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (hready : plan.BankReady S)
    (hsrc : S.R plan.src = cstream (prime+K) w (paddedCoreGatherPayload ((2^d)^c) width radius L Fs))
    (depth : ℕ) :
    ∃ rows : Fin ((2^d)^c) → Fin (2^d) → List GaussianInt,
      (∀ i j, (rows i j).length = L) ∧
      (∀ i : Fin (coreGatherIndices s width radius L).length,
        (List.ofFn fun j => cstream (prime+K) w (rows (paddedCoreIndex hcapacity i) j)).flatten =
          cstream (prime+K) w (Fs.map (packedInterval
            (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ plan.inverseCost S ∧
        ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+plan.inverseStockAllowance)
          depth plan.inverseProgram (Host.mk v S) n
          (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
            ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten))}) := by
  let rows := fun (i : Fin ((2^d)^c)) (j : Fin (2^d)) =>
    paddedGatherRows ((2^d)^c) width radius L hcapacity Fs i (Fin.cast hreplicas.symm j)
  have hlen : ∀ i j, (rows i j).length = L := by
    intro i j
    exact paddedGatherRows_length _ _ _ _ _ _ _ _
  have hinput := paddedGatherRows_source (A := prime+K) ((2^d)^c) width radius L w hcapacity Fs
  have hcast := List.ofFn_congr hreplicas (fun j : Fin Fs.length => cstream (prime+K) w
    (List.ofFn fun i => paddedGatherRows ((2^d)^c) width radius L hcapacity Fs i j).flatten)
  rw [hcast] at hinput
  refine ⟨rows,hlen,?_,?_⟩
  · intro i
    have h := paddedGatherRows_supplier (A := prime+K) ((2^d)^c) width radius L w hcapacity Fs i
    have hc := List.ofFn_congr hreplicas (fun j : Fin Fs.length => cstream (prime+K) w
      (paddedGatherRows ((2^d)^c) width radius L hcapacity Fs (paddedCoreIndex hcapacity i) j))
    rw [hc] at h
    exact h
  · exact plan.inverse_exec_within body hA hW L w hpacket rows hlen v S hready (hsrc.trans hinput) depth

end ArchiveTilePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
