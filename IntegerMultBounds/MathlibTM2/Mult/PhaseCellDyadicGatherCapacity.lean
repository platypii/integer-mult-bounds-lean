module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherExponents
public import IntegerMultBounds.MathlibTM2.Host.UnaryPowerHeader

/-! Execute minimal dyadic capacity generation from the derived core exponent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

def gatherCapacityProgram : Pr P tapeCount Q (prime+K) U :=
  unaryPowerHeader (headerReg 85) capacityRows (headerReg 40) (headerReg 41)

theorem gatherCapacity_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (b depth : ℕ) (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hexponent : (S.R (headerReg 85)).length = b)
    (hcapacity : S.R capacityRows = [])
    (h40 : S.R (headerReg 40) = []) (h41 : S.R (headerReg 41) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 4*2^b+9*b+5 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(4*2^b+9*b+5))
        depth gatherCapacityProgram (mk v S) n
        (mk v' {S with R := Function.update S.R capacityRows (List.replicate (2^b) tick)}) := by
  exact unaryPowerHeader_exec_within body (headerReg 85) capacityRows (headerReg 40) (headerReg 41)
    (by
      change ([headerReg 85,headerReg 81,headerReg 40,headerReg 41]).Nodup
      simp [List.nodup_cons,headerReg_injective.eq_iff]) b depth v S hexponent hcapacity h40 h41

def gatherDimensionsProgram : Pr P tapeCount Q (prime+K) U :=
  .seq gatherExponentsProgram gatherCapacityProgram

theorem gatherDimensions_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (a rows depth : ℕ) (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hreplicas : (S.R replicaCount).length = 2^a) (hrows : (S.R realRows).length = rows)
    (hblank : ∀ i ∈ [(81 : Fin 117),84,85,40,41,42,43,44], S.R (headerReg i) = []) :
    let b := Nat.clog 2 rows
    ∃ v' n, v'.user = v.user ∧ n ≤ ((19*2^a+10)+(19*rows+9))+(4*2^b+9*b+5) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        ((2*(19*2^a+10)+2*(19*rows+9))+2*(4*2^b+9*b+5))) depth gatherDimensionsProgram (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          (headerReg 84) (List.replicate a tick)) (headerReg 85) (List.replicate b tick))
          capacityRows (List.replicate (2^b) tick))}) := by
  dsimp only
  have hi := headerReg_injective
  have hcap : capacityRows = headerReg 81 := rfl
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := gatherExponents_exec_within body a rows depth v S hreplicas hrows
    (by intro i hi; apply hblank; simpa only [List.mem_cons,List.not_mem_nil,or_false] using Or.inr hi)
  let M : Stacks tapeCount (prime+K) := {S with R := (Function.update
    (Function.update S.R (headerReg 84) (List.replicate a tick)) (headerReg 85) (List.replicate (Nat.clog 2 rows) tick))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := gatherCapacity_exec_within body (Nat.clog 2 rows) depth v₁ M
    (by simp [M])
    (by simpa [M,hcap,hi.eq_iff] using hblank 81 (by simp))
    (by simpa [M,hi.eq_iff] using hblank 40 (by simp))
    (by simpa [M,hi.eq_iff] using hblank 41 (by simp))
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    by simpa only [gatherDimensionsProgram,M] using mn_seq_within_add he₁ he₂⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
