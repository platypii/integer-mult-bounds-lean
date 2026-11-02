module

public import IntegerMultBounds.MathlibTM2.Host.UnaryBitLength
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherHeaders

/-! Derive both routing exponents from the actual retained replica and core
counts. Original counts survive and one arithmetic workspace serves both. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

def gatherExponentsProgram : Pr P tapeCount Q (prime+K) U :=
  .seq (unaryPowerExponent replicaCount (headerReg 84) (headerReg 40) (headerReg 41)
    (headerReg 42) (headerReg 43) (headerReg 44))
    (unaryBitLength true realRows (headerReg 85) (headerReg 40) (headerReg 41)
      (headerReg 42) (headerReg 43) (headerReg 44))

theorem gatherExponents_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (a rows depth : ℕ) (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hreplicas : (S.R replicaCount).length = 2^a) (hrows : (S.R realRows).length = rows)
    (hblank : ∀ i ∈ [(84 : Fin 117),85,40,41,42,43,44], S.R (headerReg i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (19*2^a+10)+(19*rows+9) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(19*2^a+10)+2*(19*rows+9))) depth gatherExponentsProgram (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R (headerReg 84) (List.replicate a tick))
          (headerReg 85) (List.replicate (Nat.clog 2 rows) tick))}) := by
  have hi := headerReg_injective
  have hrep : replicaCount = headerReg 83 := rfl
  have hcore : realRows = headerReg 80 := rfl
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryPowerExponent_exec_within (body := body)
    replicaCount (headerReg 84) (headerReg 40) (headerReg 41) (headerReg 42) (headerReg 43) (headerReg 44)
    (by simp [hrep,List.nodup_cons,hi.eq_iff]) a v S hreplicas
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> simp) depth
  let M : Stacks tapeCount (prime+K) := {S with R := Function.update S.R (headerReg 84) (List.replicate a tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryCeilLog_exec_within (body := body)
    realRows (headerReg 85) (headerReg 40) (headerReg 41) (headerReg 42) (headerReg 43) (headerReg 44)
    (by simp [hcore,List.nodup_cons,hi.eq_iff]) rows v₁ M
    (by simpa [M,hcore,hi.eq_iff] using hrows)
    (by
      intro i hi'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [M,hi.eq_iff] using hblank _ (by simp)) depth
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    by simpa only [gatherExponentsProgram,M] using mn_seq_within_add he₁ he₂⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
