module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallRecoverySeedHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryMasterValues

/-! Wire the thirteen seed sources from ten computed masters and three ordinary
p/W/N headers. One structural membership split supplies all seed readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T A : ℕ} [NeZero s]

def recoveryMasterIndex (k : Fin 392) : Fin 10 :=
  if k = 114 then 0 else if k = 101 then 1 else if k = 112 then 2 else
  if k = 108 then 3 else if k = 97 then 4 else if k = 98 then 5 else
  if k = 99 then 6 else if k = 100 then 7 else if k = 111 then 8 else 9

def recoverySeedSources (ports : Fin 10 → Fin T) (precision packet replicas : Fin T) (k : Fin 392) : Fin T :=
  if k = 129 then precision else if k = 130 then packet else if k = 390 then replicas else
    ports (recoveryMasterIndex k)

omit [NeZero s] in
theorem recoverySeedSources_ne (ports : Fin 10 → Fin T) (precision packet replicas k : Fin T)
    (hports : ∀ i, ports i ≠ k) (hp : precision ≠ k) (hW : packet ≠ k) (hN : replicas ≠ k)
    (i : Fin 392) : recoverySeedSources ports precision packet replicas i ≠ k := by
  unfold recoverySeedSources
  split_ifs <;> first | assumption | exact hports _

theorem recoverySeedSources_master (ports : Fin 10 → Fin T) (precision packet replicas : Fin T) (i : Fin 10) :
    recoverySeedSources ports precision packet replicas (recoveryMasterPort i) = ports i := by
  fin_cases i <;> rfl

theorem recoverySeedHeader_master (H : ReplicaHaloProblem s) (W N : ℕ) (i : Fin 10) :
    recoverySeedHeader H W N (recoveryMasterPort i) = recoveryMasterValues H i := by
  fin_cases i <;> rfl

theorem recoverySeedHeaderPorts_perm : recoverySeedHeaderPorts.Perm
    (List.ofFn recoveryMasterPort++[129,130,390]) := by decide +kernel

theorem recoverySeedSources_ready (H : ReplicaHaloProblem s) (W N : ℕ)
    (ports : Fin 10 → Fin T) (precision packet replicas : Fin T) (S : Stacks T A)
    (hmasters : ∀ i, (S.R (ports i)).length = recoveryMasterValues H i)
    (hp : (S.R precision).length = H.p) (hW : (S.R packet).length = W)
    (hN : (S.R replicas).length = N) :
    ∀ k ∈ recoverySeedHeaderPorts,
      (S.R (recoverySeedSources ports precision packet replicas k)).length = recoverySeedHeader H W N k := by
  intro k hk
  have hm := List.mem_append.mp (recoverySeedHeaderPorts_perm.mem_iff.mp hk)
  rcases hm with hm | hm
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
    rw [recoverySeedSources_master,recoverySeedHeader_master]
    exact hmasters i
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · simpa [recoverySeedSources,recoverySeedHeader,derivedRecoveryHeaderPorts,complexRecoveryHeader] using hp
    · simpa [recoverySeedSources,recoverySeedHeader,derivedRecoveryHeaderPorts,complexRecoveryHeader] using hW
    · simpa [recoverySeedSources,recoverySeedHeader,derivedRecoveryHeaderPorts,complexRecoveryHeader] using hN

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
