import IntegerMultBounds.Machine.ActivePrefixStageHeadersOps
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersDivision

/-! Fixed constants and exact quotients extend the original28 marked-header
caller with the same physically clean15 private workspace. -/
namespace IntegerMultBounds.Machine.CompactChildHeadersArithmetic
noncomputable section
open ActiveRepairRankHeadersCommands
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

inductive Op where
  | existing (op : ActivePrefixStageHeadersOps.Op)
  | constant (dst : Fin 28) (value : ℕ)
  | quotient (focus : Fin 3 → Fin 28) (injective : Function.Injective focus)

def eval : Op → State → State
  | .existing op, st => ActivePrefixStageHeadersOps.eval op st
  | .constant dst n, st => put st dst n
  | .quotient f _, st => put st (f 2) ((st (f 0)).getD 0 / (st (f 1)).getD 0)

def valid : Op → State → Prop
  | .existing op, st => ActivePrefixStageHeadersOps.valid op st
  | .constant dst _, st => st dst = none
  | .quotient f _, st => ∃ n d, st (f 0)=some n ∧ st (f 1)=some d ∧ st (f 2)=none ∧ 0 < d

def program : Op → Σ k, Program 43 k a
  | .existing op => ActivePrefixStageHeadersOps.program op
  | .constant dst n => ⟨_,extend (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) n)
      (FiniteReturnStackAt.placement dst)) 15⟩
  | .quotient f hf => ⟨_,CompactGadgetReservationHeadersDivision.program f hf⟩

def cost : Op → State → ℕ
  | .existing op, st => ActivePrefixStageHeadersOps.cost op st
  | .constant _ n, _ => RecursiveChildQuotientsConstant.cost n
  | .quotient f _, st => BinaryDescriptorDivision.cost (bits ((st (f 0)).getD 0)) (bits ((st (f 1)).getD 0))

theorem runs (op : Op) (st : State) (hv : valid op st) :
    HoareTime (program (a := a) op).2 (fun x => x=bank st)
      (fun x => x=bank (eval op st)) (cost op st) := by
  cases op with
  | existing op => exact ActivePrefixStageHeadersOps.runs op st hv
  | constant dst n =>
    change st dst = none at hv
    have hi := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) n)
      (FiniteReturnStackAt.placement dst) (caller (a := a) st)
      (by rw [FiniteReturnStackAt.active_bank]; simp [caller,hv])
    have hr : HoareTime (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) n)
        (FiniteReturnStackAt.placement dst)) (fun x => x=caller st)
        (fun x => x=caller (put st dst n)) (RecursiveChildQuotientsConstant.cost n) := by
      apply hi.consequence (fun _ h => h) _ le_rfl
      rintro z ⟨small,rfl,rfl⟩
      rw [put_caller,FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    exact hoare_extend_eq hr (SharedBank.empty 15 a)
  | quotient f hf =>
    obtain ⟨n,d,hn,hd,hz,hpos⟩ := hv
    have hr := CompactGadgetReservationHeadersDivision.divides (caller (a := a) st) f hf
      (bits n) (bits d) (by simpa only [RecursiveChildQuotientsConstant.bits_value] using hpos)
      (by simp [caller,hn]) (by simp [caller,hn])
      (by simp [caller,hd]) (by simp [caller,hd])
      (by simp [caller,hz]) (by simp [caller,hz])
    simpa [program,eval,cost,hn,hd,bank,put_caller,CompactGadgetReservationHeadersCore.bank,
      RecursiveChildQuotientsConstant.bits_value] using hr

def compile : List Op → Σ k, Program 43 k a
  | [] => ⟨1,skip 43 a (by decide)⟩
  | op::ops => ⟨_,seq (program op).2 (compile ops).2⟩
def execute : List Op → State → State
  | [], st => st
  | op::ops, st => execute ops (eval op st)
def validSchedule : List Op → State → Prop
  | [], _ => True
  | op::ops, st => valid op st ∧ validSchedule ops (eval op st)
def scheduleCost : List Op → State → ℕ
  | [], _ => 0
  | op::ops, st => cost op st+1+scheduleCost ops (eval op st)

theorem schedule_runs (ops : List Op) (st : State) (hv : validSchedule ops st) :
    HoareTime (compile (a := a) ops).2 (fun x => x=bank st)
      (fun x => x=bank (execute ops st)) (scheduleCost ops st) := by
  induction ops generalizing st with
  | nil => exact skip_hoare (by decide) (bank st)
  | cons op ops ih => exact (runs op st hv.1).seq (ih (eval op st) hv.2)

end
end IntegerMultBounds.Machine.CompactChildHeadersArithmetic
