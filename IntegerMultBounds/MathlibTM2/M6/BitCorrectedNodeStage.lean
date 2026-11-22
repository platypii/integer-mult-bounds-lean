module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepAllocatedReturn
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner

/-! Read the recursive PR589 stage handoff in the parent node's coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)

/-- A correction can read the conversion's exact right stacks directly. The
spare owner retains its incoming representation throughout the conversion. -/
theorem correctionAfterSweep_exec {w B W T Q : ℕ} {P U : Type}
    (parent : Fin 64 → ZMod (prime^w)) (units : ∀ i, IsUnit (parent i)) (n : Fin 9)
    (stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := (prime^w)^16*(B*((prime^w)^112*W)))))
    (chart : Fin stage.tapes ↪ Fin T) (slots : Fin 142081 ↪ Fin T)
    (placed : ∀ i, chart (stage.slots i) = slots i) (fits : stage.states ≤ Q)
    (body : P → Pr P T Q prime U) (x : OwnerArray w B W) (u : HS T Q prime U) (S : Stacks T prime)
    (privateReady : ChartPrivateReady stage (embStk chart S))
    (left : ∀ r, S.L (slots (sweepRoleTape r)) = [])
    (words : ∀ r, S.R (slots (sweepRoleTape r)) = List.ofFn (fun i =>
      SparseRoleCircuit.encode (a := prime) (sweepArray parent units n x (sweepRoleTape r) i)))
    (extra : WordAtZero (x (Fin.last 142080)) (S.L (slots (Fin.last 142080)))
      (S.R (slots (Fin.last 142080)))) :
    ∃ z F t, Exec body (embProg chart Empty.elim (foreign (liftQ stage.program fits)))
        (mk u S) t (mk z F) ∧ t ≤ stage.cost*(stage.tapes+5)+6 ∧ z.user = u.user ∧
      RepT (phaseOwners (stage.transform (sweepArray parent units n x))) (embStk slots F).L (embStk slots F).R ∧
      ∀ j, (∀ i, chart i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let data := sweepArray parent units n x
  have input : RepT (phaseOwners data) (embStk slots S).L (embStk slots S).R := by
    intro i h
    change putWord (fun _ => blank) 0 _ h = readAt blank (S.L (slots i)) (S.R (slots i)) (h-0)
    rw [sub_zero]
    induction i using Fin.lastCases with
    | last => exact (extra h).symm
    | cast j =>
      let index := (Fintype.equivFin Role).trans (finCongr card_role)
      let r := index.symm j
      have port : sweepRoleTape r = j.castSucc := congrArg Fin.castSucc (index.apply_symm_apply j)
      rw [← port,left r,words r,readAt_nil_left,putWord_blank_zero]
  have align : (⇑chart ∘ stage.slots) = slots := funext placed
  obtain ⟨z,F,t,exec,paid,user,_,output,_,frame⟩ :=
    ownerStage_exec_emb stage chart fits body data u S privateReady (align ▸ input)
  exact ⟨z,F,t,exec,paid,user,align ▸ output,frame⟩

/-- Pad the corrected compact bank into the recursive stage's input fan,
including the extra owner. All owners reuse one set of padding counters. -/
theorem padPlacedCorrection_exec {T Q w B K : ℕ} {P U : Type}
    (port : Fin 142081 → Fin 12 ↪ Fin T)
    (shared : ∀ i k j, j ≠ 0 → j ≠ 1 → port i j = port k j)
    (separate : ∀ i k, i ≠ k → ∀ j, port i j ≠ port k 0 ∧ port i j ≠ port k 1) (fits : 215 ≤ Q)
    (body : P → Pr P T Q prime U) (hb : 0 < B) (hk : 0 < K) :
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let frame := ownerPadFrame (A*B) N K
    ∃ code, ∀ (dst : Fin (142081+2) ↪ Fin T)
      (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) u S,
      (∀ i, dst (i.castAdd 2) = port i 1) →
      (∀ (j : Fin 2) i h, port i h ≠ dst (j.natAdd 142081)) →
      StageControls dst (A*(B*N*K)) S →
      (∀ j : Fin 12, j ≠ 0 → j ≠ 1 → ∀ z,
        frame.tape j z = readAt blank (S.L (port 0 j)) (S.R (port 0 j)) (z-frame.head j)) →
      RepT (phaseOwners x) (fun i => S.L (port i 0)) (fun i => S.R (port i 0)) →
      (∀ i z, readAt blank (S.L (port i 1)) (S.R (port i 1)) z = blank) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ t ≤ 142081*(7021*(A*B)*(N*K)+6)+1 ∧
        z.user = u.user ∧ HelperFan dst (singleLabelBank (firstRowLabel w) x) F ∧
        ∀ j, (∀ i h, port i h ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro A N frame
  let order := List.finRange 142081
  refine ⟨Prog.seqList (order.map (fun i => embProg (port i) (Empty.elim : Empty → P)
    (foreign (liftQ RowPaddingConstructedAlphabet.program fits)))),?_⟩
  intro dst x u S placed apart ctrl headers compact empty
  obtain ⟨z,F,t,run,paid,user,_,payload,off⟩ :=
    ownerPads_exec (w := w) hb hk port shared separate fits body x order (List.nodup_finRange _) u S headers
      (by intro i _ j; rw [encodedOwnerCell]; exact (compact i j).symm) (fun i _ => empty i)
  refine ⟨z,F,t,run,by simpa [order] using paid,user,?_,fun j h => off j (fun i _ => h i)⟩
  intro i
  refine Fin.addCases (fun j z => ?_) (fun j z => ?_) i
  · have read := payload j (List.mem_finRange j) z
    rw [encodedOwnerCell] at read
    simp only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,placed]
    change putWord _ 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime)
      (singleLabelBank (B := B) (K := K) (firstRowLabel w) x j i)) z = _
    exact read.symm
  · obtain ⟨hl,hr⟩ := off _ (fun i _ h => apart j i h)
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls,
      ite_self,embStk,Function.comp_apply,hl,hr] using ctrl j z

theorem padCorrectionOwners_exec {T Q w B K : ℕ} {P U : Type}
    (fan : Fin (142081+2) ↪ Fin T) (fits : 215 ≤ Q)
    (body : P → Pr P ((T+142081*7)+142081+10) Q prime U) (hb : 0 < B) (hk : 0 < K) :
    let port := stagePadPort fan
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let frame := ownerPadFrame (A*B) N K
    ∃ code, ∀ (dst : Fin (142081+2) ↪ Fin ((T+142081*7)+142081+10))
      (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) u S,
      (∀ i, dst (i.castAdd 2) = port i 1) →
      (∀ (j : Fin 2) i h, port i h ≠ dst (j.natAdd 142081)) →
      StageControls dst (A*(B*N*K)) S →
      (∀ j : Fin 12, j ≠ 0 → j ≠ 1 → ∀ z,
        frame.tape j z = readAt blank (S.L (port 0 j)) (S.R (port 0 j)) (z-frame.head j)) →
      RepT (phaseOwners x) (fun i => S.L (port i 0)) (fun i => S.R (port i 0)) →
      (∀ i z, readAt blank (S.L (port i 1)) (S.R (port i 1)) z = blank) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ t ≤ 142081*(7021*(A*B)*(N*K)+6)+1 ∧
        z.user = u.user ∧ HelperFan dst (singleLabelBank (firstRowLabel w) x) F ∧
        ∀ j, (∀ i h, port i h ≠ j) → F.L j = S.L j ∧ F.R j = S.R j :=
  padPlacedCorrection_exec (stagePadPort fan) (stagePadPort_shared fan) (stagePadPort_apart fan) fits body hb hk

/-- The same entry and exit corrections work for every parent and every node
array. The recursive stage runs on the occupied label row and its output,
after correction and return to node order, has the required stage action. -/
theorem correctedNodeStage_exec [M8.Machine.Net] :
    ∃ C : ℝ, ∀ (n : Fin 9) (w B W : ℕ), 0 < w → 0 < B*((prime^w)^112*W) →
      let V := (prime^w)^16*(B*((prime^w)^112*W))
      ∃ enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        ((enter.cost+leave.cost : ℕ) : ℝ) ≤ C*(w : ℝ)^M8.Machine.BudgetBound.tau*V ∧
        ∀ (parent : Fin 64 → ZMod (prime^w)) (units : ∀ i, IsUnit (parent i))
          {P U : Type} {t q : ℕ} {body : P → Pr P t q prime U} {code src dst prepared price post},
        StageHandoffExec n w B W body code src dst prepared price post →
        ∀ (x : OwnerArray w B W) u S,
        let entry := singleLabelBank (B := B) (K := (prime^w)^112*W) (firstRowLabel w)
        HelperFan src (entry (enter.transform (sweepArray parent units n x))) S →
        (∀ j, (∀ i, src i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
        ∃ z F steps y, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ price ∧ z.user = u.user ∧
          HelperFan dst (entry y) F ∧ post F ∧ ∀ b j,
            let addr := fun v => nodeWindowEquiv w B W parent units (b,windowState w v,j)
            readRoles addr (nodeArray parent units n (leave.transform y)) =
              (Piece.stage n).run (readRoles addr x) := by
  obtain ⟨C,_,correct⟩ := correctedSweep_read
  refine ⟨C,?_⟩
  intro n w B W hw size V
  obtain ⟨enter,leave,_,_,paid,acts⟩ := correct n w B W hw size
  refine ⟨enter,leave,paid,?_⟩
  intro parent units P U t q body code src dst prepared price post run x u S entry live frame
  obtain ⟨z,F,steps,packed,out,exec,cost,user,ready,trace,done⟩ := run _ u S live frame
  refine ⟨z,F,steps,_,exec,cost,user,ready,done,?_⟩
  intro b j addr
  exact (nodeArray_read parent units n _ b j).trans
    ((acts _ _ ⟨packed,out,trace,rfl⟩ b j).trans
      (congrArg (Piece.stage n).run (sweepArray_read parent units n x b j)))

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile
