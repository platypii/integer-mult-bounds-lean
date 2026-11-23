module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordCleanup
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.TapeCharge
public import IntegerMultBounds.MathlibTM2.Host.Foreign
import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock
import IntegerMultBounds.MathlibTM2.Host.ForeignStock
public import IntegerMultBounds.Networks.Shared50ModularControl

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Fast.Main
open Shared50ModularControl (prime)

/-- Elapsed steps plus the change in cleanup cost on any set of tapes. -/
def CleanupBound {T : ℕ} (S F : Stacks T prime) (steps budget : ℕ) : Prop :=
  ∀ js : List (Fin T), js.Nodup →
    steps+tapeCharge (fun l r => 4*l.length+2*r.length+4) js F ≤
      tapeCharge (fun l r => 4*l.length+2*r.length+4) js S+budget

theorem CleanupBound.seq {T : ℕ} {S D F : Stacks T prime} {n m a b : ℕ}
    (left : CleanupBound S D n a) (right : CleanupBound D F m b) : CleanupBound S F (n+m) (a+b) := by
  intro js distinct
  have := left js distinct
  have := right js distinct
  omega

theorem CleanupBound.place {T H : ℕ} (bank : Fin T ↪ Fin H) {S F : Stacks H prime} {n price : ℕ}
    (off : ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j)
    (bound : CleanupBound (embStk bank S) (embStk bank F) n price) : CleanupBound S F n price :=
  placedCleanup_cost_le bank S F _ n price off bound

/-- Project the execution estimate onto time alone, or include tape cleanup. -/
def workerCost (charged : Bool) {T : ℕ} (S F : Stacks T prime) (steps budget : ℕ) : Prop :=
  if charged then CleanupBound S F steps budget else steps ≤ budget

def nativePrice (charged : Bool) (steps : ℕ) := if charged then 13*steps else steps

theorem workerCost.weaken {charged T S F steps a b} (cost : workerCost charged (T := T) S F steps a)
    (le : a ≤ b) : workerCost charged S F steps b := by
  cases charged
  · exact Nat.le_trans cost le
  · exact fun js h => (cost js h).trans (Nat.add_le_add_left le _)

theorem workerCost.seq {charged T S D F n m a b} (left : workerCost charged (T := T) S D n a)
    (right : workerCost charged D F m b) : workerCost charged S F (n+m) (a+b) := by
  cases charged
  · exact Nat.add_le_add left right
  · exact CleanupBound.seq left right

private theorem nativeExecution {K P σ : Type} {Γ : K → Type} [DecidableEq K]
    {body : P → Prog P Γ σ} {p s t n c} (run : Exec body p s n t) (bound : mnNativePushBound c p) :
    Exec (fun _ => .act .done) p s n t := by
  induction run with
  | act => exact .act _ _
  | seq _ _ a b => exact .seq (a bound.1) (b bound.2)
  | cond_true h _ a => exact .cond_true h (a bound.1)
  | cond_false h _ a => exact .cond_false h (a bound.2)
  | loop_false h => exact .loop_false h
  | loop_true h _ _ a b => exact .loop_true h (a bound) (b bound)
  | call => exact bound.elim

theorem nativeCleanupBound {P U : Type} {T Q c : ℕ} {body : P → Pr P T Q prime U}
    {prog u v S F n} (exec : Exec body prog (mk u S) n (mk v F)) (native : mnNativePushBound c prog) :
    CleanupBound S F n ((1+6*c)*n) := by
  intro js unique
  have push {K P σ : Type} {Γ : K → Type} (p : Prog P Γ σ) (h : mnNativePushBound c p) : mnProgPush p ≤ c := by
    induction p with
    | act => exact h
    | seq _ _ a b | cond _ _ _ a b => exact max_le (a h.1) (b h.2)
    | loop _ _ a => exact a h
    | call => exact h.elim
  have bill := recordCleanup_cost_le js unique (nativeExecution exec native) (push _ native) (fun _ => Nat.zero_le c)
  change tapeCharge (fun l r => 4*l.length+2*r.length+4) js F+1 ≤ tapeCharge (fun l r => 4*l.length+2*r.length+4) js S+1+6*(c*n) at bill
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
  omega

theorem foreignCleanupBound {P U : Type} {T t Q : ℕ} {bank : Fin t ↪ Fin T} {prog : Program t Q prime}
    {body : P → Pr P T Q prime U} {u v S F n}
    (exec : Exec body (embProg bank Empty.elim (foreign prog)) (mk u S) n (mk v F))
    : CleanupBound S F n (13*n) := by
  exact nativeCleanupBound exec (embProg_native (e := (bank : Fin t → Fin T)) (Empty.elim : Empty → P)
    (foreign (U := U) prog) (foreign_native _))

theorem placedClosedWorkerCost {P U : Type} {T t Q : ℕ} (bank : Fin t ↪ Fin T)
    (prog : Pr Empty t Q prime U) (charged : Bool) :
    ∃ rate : ℕ, ∀ (body : P → Pr P T Q prime U) u v S F n,
      Exec body (embProg bank Empty.elim prog) (mk u S) n (mk v F) → workerCost charged S F n (rate*n) := by
  cases charged
  · exact ⟨1,fun _ _ _ _ _ _ _ => (Nat.one_mul _).symm.le⟩
  · exact ⟨_,fun _ _ _ _ _ _ run => nativeCleanupBound run
      (embProg_native (e := (bank : Fin t → Fin T)) (Empty.elim : Empty → P) prog (WordCmd.empty_native prog))⟩

theorem foreignWorkerCost {P U : Type} {T t Q : ℕ} {bank : Fin t ↪ Fin T} {prog : Program t Q prime}
    {body : P → Pr P T Q prime U} {u v S F n} (charged : Bool)
    (exec : Exec body (embProg bank Empty.elim (foreign prog)) (mk u S) n (mk v F)) :
    workerCost charged S F n (nativePrice charged n) := by
  cases charged
  · exact le_rfl
  · exact foreignCleanupBound exec

end IntegerMultBounds.MathlibTM2.M6.BitNode
