module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicMasterValues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateRecoverySeedSources

/-! A fitting batch generates one numerical master bank. Its empty right
piece aliases the shared masters and a permanent empty endpoint source. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def zeroEndpointSources {T : ℕ} (ports : Fin 10 → Fin T) (zero : Fin T) (i : Fin 10) : Fin T :=
  if i.val < 8 then ports i else zero

/-- Wire the empty piece from already generated masters, using structural
seed-port membership rather than enumerating the 392-register source bank. -/
theorem zeroEndpointSeedSources_ready {s T A : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (ports : Fin 10 → Fin T) (zero precision packet replicas : Fin T) (W N : ℕ) (S : Stacks T A)
    (hmasters : ∀ i, (S.R (ports i)).length = recoveryMasterValues H i)
    (hrelation : ∀ i, recoveryMasterValues K i = if i.val < 8 then recoveryMasterValues H i else 0)
    (hzero : S.R zero = []) (hp : (S.R precision).length = K.p)
    (hW : (S.R packet).length = W) (hN : (S.R replicas).length = N) :
    ∀ k ∈ recoverySeedHeaderPorts,
      (S.R (recoverySeedSources (zeroEndpointSources ports zero) precision packet replicas k)).length =
        recoverySeedHeader K W N k := by
  apply recoverySeedSources_ready K W N _ precision packet replicas S _ hp hW hN
  intro i
  rw [hrelation i]
  unfold zeroEndpointSources
  split_ifs with hi
  · exact hmasters i
  · simp only [hzero,List.length_nil]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
