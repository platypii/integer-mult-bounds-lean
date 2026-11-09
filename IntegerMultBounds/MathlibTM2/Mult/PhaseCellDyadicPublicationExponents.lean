module

public import IntegerMultBounds.MathlibTM2.Host.UnaryDyadicExponents
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicPublicationHeaders

/-! Publication orders core and replica exponents oppositely to gather. Both
layouts instantiate the same restoring unary-count algorithm. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

def publicationExponentsProgram : Pr P tapeCount Q (prime+K) U :=
  unaryDyadicExponents replicaCount realRows (headerReg 85) (headerReg 84)
    (headerReg 40) (headerReg 41) (headerReg 42) (headerReg 43) (headerReg 44)

def publicationExponentRegisters : List (Fin tapeCount) := [headerReg 85,headerReg 84]

def publicationExponentsState (b N : ℕ) (S : Stacks tapeCount (prime+K)) :=
  {S with R := (Function.update (Function.update S.R (headerReg 85) (List.replicate b tick))
    (headerReg 84) (List.replicate (Nat.clog 2 N) tick))}

theorem publicationExponents_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (b N depth : ℕ) (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hreplicas : (S.R replicaCount).length = 2^b) (hrows : (S.R realRows).length = N)
    (hblank : ∀ i ∈ [(85 : Fin 117),84,40,41,42,43,44], S.R (headerReg i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (19*2^b+10)+(19*N+9) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(19*2^b+10)+2*(19*N+9))) depth publicationExponentsProgram (mk v S) n
        (mk v' (publicationExponentsState b N S)) := by
  exact unaryDyadicExponents_exec_within (body := body)
    replicaCount realRows (headerReg 85) (headerReg 84)
    (headerReg 40) (headerReg 41) (headerReg 42) (headerReg 43) (headerReg 44)
    (by
      change ([headerReg 83,headerReg 80,headerReg 85,headerReg 84,
        headerReg 40,headerReg 41,headerReg 42,headerReg 43,headerReg 44]).Nodup
      simp [List.nodup_cons,headerReg_injective.eq_iff]) b N depth v S hreplicas hrows
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> simp)

theorem publicationExponentsState_off (b N : ℕ) (S : Stacks tapeCount (prime+K))
    (i : Fin tapeCount) (hi : i ∉ publicationExponentRegisters) :
    (publicationExponentsState b N S).R i = S.R i := by
  simp only [publicationExponentRegisters,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  simp only [publicationExponentsState,Function.update_of_ne hi.2,Function.update_of_ne hi.1]


end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
