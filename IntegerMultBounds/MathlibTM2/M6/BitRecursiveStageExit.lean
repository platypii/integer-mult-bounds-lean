module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepExitReturn

/-! Run the recursive PR589 handoff and return its result on the enclosing machine. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover Cover.Fallback RingFormula Node
open Shared50ModularControl (prime)

theorem recursiveStageExit_exec {P U : Type} {Q t : ℕ} (n : Fin 9) (src fan : Fin (142081+2) ↪ Fin t)
    (fits : 215 ≤ Q) :
    ∃ C : ℕ, ∀ (w H B W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
    let M := prime^(w+1)
    let K := M^112*W
    let A := M^16
    let N := prime^(64*((w+1)*64))
    M^128 < 2^H → H ≤ M^128+1 → 0 < B → 0 < W →
    ∀ (leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := A*(B*K)))),
    leave.states ≤ Q → ∀ (inner : P → Pr P t Q prime U) (worker : Pr P t Q prime U) prepared price,
    StageHandoffExec n (w+1) B W inner worker src fan prepared price →
    let recBank := recursive t leave.tapes
    let body := fun f => embProg recBank id (inner f)
    let crop := port fan leave.slots
    let sw := sweep t leave.tapes
    let dest := owners.trans sw
    let scratch := tmp t leave.tapes
    ∃ code, ∀ x u S, HelperFan (src.trans recBank) (singleLabelBank (firstRowLabel (w+1)) x) S →
      (∀ j, (∀ i, src i ≠ j) → S.L (recBank j) = prepared.L j ∧ S.R (recBank j) = prepared.R j) →
      ChartPrivateReady leave (embStk (chart t leave.tapes) S) → CropCounters (crop 0) (A*B) N K S →
      (∀ i z, readAt blank (S.L (crop i 1)) (S.R (crop i 1)) z = blank) →
      S.L scratch = [] → S.R scratch = [] → (∀ i, S.R (dest i) = []) →
      ReturnHeaders w H parent W B (embStk sw S).R →
      ∃ z F l y, Exec body code (mk u S) l (mk z F) ∧
        l ≤ price + (142081*(7021*(A*B)*(N*K)+6)+1 + (leave.cost*(leave.tapes+5)+6) +
          (142081*(8*(A*(B*K))+10)+1) + (142080*(C*(A*(B*N*K))+8)+1)) ∧
        z.user = u.user ∧ sweepEffect n (w+1) B W x y ∧ ∀ r, F.R (dest (sweepRoleTape r)) = List.ofFn fun i =>
          SparseRoleCircuit.encode (nodeArray parent units n (leave.transform y) (sweepRoleTape r) i) := by
  obtain ⟨C,finish⟩ := stageExitReturn_exec (P := P) (U := U) n fan fits
  refine ⟨C,?_⟩
  intro w H B W parent units M K A N hw bound hb hwid leave room inner worker prepared price handoff
    recBank body crop sw dest scratch
  obtain ⟨exitCode,exitRun⟩ := finish w H B W parent units hw bound hb hwid leave room body
  refine ⟨(embProg recBank id worker).seq exitCode,?_⟩
  intro x u S live stock ready counters cropBlank left right fresh headers
  obtain ⟨a,E,m,y,run,paid,user,rep,effect⟩ := handoff.toPiece x (embDn recBank u) (embStk recBank S) live stock
  obtain ⟨v,D,placed,_,same,view,off⟩ := exec_emb (ι := id) (body' := body) recBank.injective
    (fun _ => rfl) run u rfl S rfl
  have chartOff j := off (chart t leave.tapes j) (fun i =>
    (Fintype.equivFin (Register t leave.tapes)).injective.ne (show Register.recursive i ≠ .chart j by intro h; cases h))
  have sweepOff j := off (sw j) (fun i =>
    (Fintype.equivFin (Register t leave.tapes)).injective.ne (show Register.recursive i ≠ .sweep j by intro h; cases h))
  have scratchOff := off scratch (fun i =>
    (Fintype.equivFin (Register t leave.tapes)).injective.ne (show Register.recursive i ≠ .crop 0 by intro h; cases h))
  have ready' : ChartPrivateReady leave (embStk (chart t leave.tapes) D) := by
    intro j priv h
    change _ = readAt blank (D.L _) (D.R _) _
    rw [(chartOff j).1,(chartOff j).2]
    exact ready j priv h
  have counters' : CropCounters (crop 0) (A*B) N K D := by
    intro j h d z
    have samePort : crop 0 j = (Fintype.equivFin (Register t leave.tapes)) (.crop j) := by
      change (Fintype.equivFin (Register t leave.tapes)) (cropReg fan leave.slots 0 j) = _
      simp [cropReg,h,d]
    have kept := off (crop 0 j) (fun i => by
      rw [samePort]
      exact (Fintype.equivFin (Register t leave.tapes)).injective.ne (show Register.recursive i ≠ .crop j by intro e; cases e))
    rw [kept.1,kept.2]
    exact counters j h d z
  have rightEq : (embStk sw D).R = (embStk sw S).R := funext fun j => (sweepOff j).2
  rw [← view] at rep
  obtain ⟨z,F,l,back,bill,hz,out⟩ := exitRun y v D rep ready' counters' (by
    intro i h
    change readAt blank (D.L (chart t leave.tapes (leave.slots i))) (D.R (chart t leave.tapes (leave.slots i))) h = _
    rw [(chartOff _).1,(chartOff _).2]
    exact cropBlank i h) (scratchOff.1.trans left) (scratchOff.2.trans right)
    (fun i => (sweepOff (owners i)).2.trans (fresh i)) (rightEq ▸ headers)
  exact ⟨z,F,m+l,y,Exec.seq placed back,Nat.add_le_add paid bill,hz.trans (same.trans user),effect,out⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
