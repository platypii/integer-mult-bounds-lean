module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepEntryRun
public import IntegerMultBounds.MathlibTM2.M6.BitRecursiveStageExit

/-! Execute a prepared PR589 stage from parent addresses back to parent addresses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover
open Shared50ModularControl (prime)

theorem placedStage_exec [M8.Machine.Net] {P U : Type} {t Q : ℕ} (n : Fin 9) (src dst : Fin (142081+2) ↪ Fin t)
    (fits : 215 ≤ Q) :
    ∃ (C : ℕ) (chartRate : ℝ), ∀ w H B W (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
    let M := prime^(w+1)
    let K := M^112*W
    let A := M^16
    let N := prime^(64*((w+1)*64))
    let V := A*(B*N*K)
    M^128 < 2^H → H ≤ M^128+1 → 0 < B → 0 < W →
    ∃ enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := A*(B*K))),
    ((enter.cost+leave.cost : ℕ) : ℝ) ≤ chartRate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*((A*(B*K) : ℕ) : ℝ) ∧
    (
    enter.states ≤ Q → leave.states ≤ Q →
    ∀ (inner : P → Pr P t Q prime U) worker prepared price,
    StageHandoffExec n (w+1) B W inner worker src dst prepared price →
    let recBank := recursive t leave.tapes
    let mid := size t leave.tapes
    let outer := recursive mid enter.tapes
    let fan := src.trans recBank
    let body := fun f => embProg outer id (embProg recBank id (inner f))
    let slots := (⟨enter.slots,enter.slots_injective⟩ : Fin 142081 ↪ Fin enter.tapes)
    let input := slots.trans (chart mid enter.tapes)
    let forward := forwardBank (t := mid) slots
    let sw := sweep t leave.tapes
    let crop := port dst leave.slots
    ∃ code, ∀ (x : OwnerArray (w+1) B W) u S,
    let D := embStk outer S
    ChartPrivateReady enter (embStk (chart mid enter.tapes) S) →
    ReturnHeaders w H parent W B (embStk forward S).R →
    (∀ r, S.L (input (sweepRoleTape r)) = []) →
    (∀ r, S.R (input (sweepRoleTape r)) = List.ofFn fun i => SparseRoleCircuit.encode (x (sweepRoleTape r) i)) →
    WordAtZero (x (Fin.last 142080)) (S.L (input (Fin.last 142080))) (S.R (input (Fin.last 142080))) →
    StageControls (fan.trans outer) V S → CropCounters (padPort fan enter.slots 0) (A*B) N K S →
    (∀ (i : Fin 142081) z, readAt blank (D.L (fan (i.castAdd 2))) (D.R (fan (i.castAdd 2))) z = blank) →
    (∀ j, (∀ i, src i ≠ j) → D.L (recBank j) = prepared.L j ∧ D.R (recBank j) = prepared.R j) →
    ChartPrivateReady leave (embStk (chart t leave.tapes) D) → CropCounters (crop 0) (A*B) N K D →
    (∀ i z, readAt blank (D.L (crop i 1)) (D.R (crop i 1)) z = blank) →
    D.L (tmp t leave.tapes) = [] → D.R (tmp t leave.tapes) = [] → (∀ i, D.R (sw (owners i)) = []) →
    ReturnHeaders w H parent W B (embStk sw D).R →
    ∃ z F l y, Exec body code (mk u S) l (mk z F) ∧
      l ≤ price + 142080*(C*V+16)+2 + 2*(142081*(7021*(A*B)*(N*K)+6)+1) +
        (enter.cost*(enter.tapes+5)+6) + (leave.cost*(leave.tapes+5)+6) + (142081*(8*(A*(B*K))+10)+1) ∧
      z.user = u.user ∧
      (∀ b j, let address := fun v => nodeWindowEquiv (w+1) B W parent units (b,windowState (w+1) v,j)
        readRoles address (nodeArray parent units n (leave.transform y)) = (Piece.stage n).run (readRoles address x)) ∧
      ∀ r, F.R (outer (sw (owners (sweepRoleTape r)))) = List.ofFn fun i =>
        SparseRoleCircuit.encode (nodeArray parent units n (leave.transform y) (sweepRoleTape r) i)) := by
  obtain ⟨D,finish⟩ := recursiveStageExit_exec (P := P) (U := U) n src dst fits
  obtain ⟨C,build⟩ := stageEntry_exec (P := P) (U := U) n fits
  obtain ⟨rate,correct⟩ := correctedSweep_read
  refine ⟨C+D,rate,?_⟩
  intro w H B W parent units M K A N V hw bound hb width
  obtain ⟨enter,leave,charts,acts⟩ := correct n (w+1) B W (by omega)
    (Nat.mul_pos hb (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) width))
  refine ⟨enter,leave,charts,?_⟩
  intro ein lout inner worker prepared price handoff
    recBank mid outer fan body slots input forward sw crop
  obtain ⟨entry,entryRun⟩ := build fan w H B W parent units hw bound hb width enter ein body
  obtain ⟨back,backRun⟩ := finish w H B W parent units hw bound hb width leave lout inner worker prepared price handoff
  refine ⟨entry.seq (embProg outer id back),?_⟩
  intro x u S start ready headers left words extra controls counters empty stock exitReady exitCounters blankDst tl tr fresh exitHeaders
  obtain ⟨v,E,k,run,paid,user,live,frame⟩ := entryRun x u S ready headers left words extra controls counters empty
  let G := embStk outer E
  let e := Fintype.equivFin (Register t leave.tapes)
  have chartKeep j := frame (chart t leave.tapes j) (fun i => e.injective.ne
    (show Register.recursive _ ≠ .chart j by intro h; cases h))
  have sweepKeep j := frame (sw j) (fun i => e.injective.ne
    (show Register.recursive _ ≠ .sweep j by intro h; cases h))
  have tmpKeep := frame (tmp t leave.tapes) (fun i => e.injective.ne
    (show Register.recursive _ ≠ .crop 0 by intro h; cases h))
  obtain ⟨a,L,l,y,exec,bill,same,effect,out⟩ := backRun _ (embDn outer v) G live (by
    intro j hj
    have kept := frame (recBank j) (fun i => recBank.injective.ne (hj _))
    exact ⟨kept.1.trans (stock j hj).1,kept.2.trans (stock j hj).2⟩) (by
    intro j hj h
    change _ = readAt blank (E.L _) (E.R _) _
    rw [(chartKeep j).1,(chartKeep j).2]; exact exitReady j hj h) (by
    intro j h d z
    have addr : crop 0 j = e (.crop j) := by
      change e (cropReg _ _ _ _) = _; simp [cropReg,h,d]
    have kept := frame (crop 0 j) (fun i => by
      rw [addr]; exact e.injective.ne (show Register.recursive _ ≠ .crop j by intro eqn; cases eqn))
    change _ = readAt blank (E.L _) (E.R _) _
    rw [kept.1,kept.2]; exact exitCounters j h d z) (by
    intro i z
    change readAt blank (E.L (outer (chart t leave.tapes _))) (E.R (outer (chart t leave.tapes _))) _ = _
    rw [(chartKeep _).1,(chartKeep _).2]; exact blankDst i z)
    (tmpKeep.1.trans tl) (tmpKeep.2.trans tr) (fun i => (sweepKeep _).2.trans (fresh i)) (by
    have eqn : (embStk sw G).R = (embStk sw start).R := funext fun j => (sweepKeep j).2
    rwa [eqn])
  obtain ⟨z,F,placed,_,hz,view,_⟩ := exec_emb (ι := id) (body' := body) outer.injective (fun _ => rfl) exec v rfl E rfl
  refine ⟨z,F,k+l,y,Exec.seq run placed,?_,hz.trans (same.trans user),?_,?_⟩
  · apply (Nat.add_le_add paid bill).trans
    dsimp only [V,A,N,K,M]
    exact le_of_eq (by ring)
  · intro b j address
    exact (nodeArray_read parent units n _ b j).trans
      ((acts _ _ effect b j).trans (congrArg (Piece.stage n).run (sweepArray_read parent units n x b j)))
  · intro r
    exact (congrArg (fun D => Stacks.R D (sw (owners (sweepRoleTape r)))) view).trans (out r)

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
