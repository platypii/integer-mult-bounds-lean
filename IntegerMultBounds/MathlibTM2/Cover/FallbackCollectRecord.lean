module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackQueuedAnchorRecord

/-! Collect a transformed live record and restore the payload workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

open Mult.ShortConv

noncomputable def collectAnchorRecord {T : ℕ} (ports : Fin (N+2) ↪ Fin T) (count src saved tmp acc : Fin T) (d : ℕ) :
    Pr P T columnCapacity prime U :=
  .seq (queuedResidual ports count src saved tmp d) (transfer count (ports (archivePorts 0 (columnBank 24))) acc tmp)

theorem collectAnchorRecord_exec {r records T : ℕ} (ports : Fin (N+2) ↪ Fin T) {count src saved tmp acc : Fin T}
    (outside : ∀ j, ports j ≠ src)
    (separate : [count,src,ports (archivePorts 0 (columnBank 24)),saved,tmp].Nodup)
    (collectPorts : [count,ports (archivePorts 0 (columnBank 24)),acc,tmp].Nodup)
    (buffer : ∀ i, ports i ≠ acc) (countOff : ∀ i, ports i ≠ count) (tmpOff : ∀ i, ports i ≠ tmp) (accSrc : acc ≠ src)
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (g : LabelPadding.Label r (w+1)) (m : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    (det : m.det = 1 ∨ m.det = -1)
    (lift : (LabelRing.res prime (w+1) (by omega)).mapMatrix m = table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    (block : ℕ) (live : block*M^(r*r)+(LabelAddress.address g).val < records)
    (inputs : ℕ → Record.Array d 1 (w+1) W) (outs : List (Record.Array d 1 (w+1) W))
    (result : (Record.signedInputs table (w+1) records inputs).Forall₂ Record.Correct outs)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P T columnCapacity prime U) (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (tail rest queueTail : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) :
    let bank := columnBank.trans (archivePorts 0)
    let dst := ports (bank 24)
    let j := block*M^(r*r)+(LabelAddress.address g).val
    let rows := classPivots (table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    let code := fun t =>
      let pivots := classPivots (table (LabelStock.residue r (w+1) 1 t))
      scheduleCode (A := prime) pivots ++ orderedScheduleCode (List.finRange (d+1)).reverse pivots
    let clean := fun (D : Stacks T prime) => ∀ i : Fin N, 35 ≤ i.val →
      D.L (ports (columnPorts i).castSucc) = [] ∧ D.R (ports (columnPorts i).castSucc) = []
    ShearReady bank H J m tail (fun _ : ZMod 2 => blank) (fun _ => blank) dest 0 q original (embStk ports S) →
    clean S → Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ original →
    S.R src = (outs.drop j).flatMap payloadWord ++ queueTail → (S.R count).length = M^(d+1)*W →
    (∀ z, readAt blank (S.L dst) (S.R dst) z = blank) → S.R saved = [] → S.R tmp = [] →
    S.R (ports (Fin.last N).castSucc) = ((List.range records).drop j).flatMap code ++ rest →
    ∃ z F n word, z.user = v.user ∧ n ≤ 6*(M^(d+1)*W)+6+(1+signedResidualTime U rows w W H J)+(4*(M^(d+1)*W)+4) ∧
      Exec body (collectAnchorRecord ports count src saved tmp acc d) (mk v S) n (mk z F) ∧
      (∀ x k, word (FlatCoordinateLayout.index (m.mulVec x) k) = original (FlatCoordinateLayout.index x k)) ∧
      F.R acc = (payloadWord (SparseRoleCircuit.encode ∘ word)).reverse ++ S.R acc ∧
      (∀ z, readAt blank (F.L dst) (F.R dst) z = blank) ∧
      ShearReady bank H J m tail (fun _ : ZMod 2 => blank) (fun _ => blank) dest 0 q original (embStk ports F) ∧
      clean F ∧ F.R (ports (Fin.last N).castSucc) = ((List.range records).drop (j+1)).flatMap code ++ rest ∧
      F.R src = (outs.drop (j+1)).flatMap payloadWord ++ queueTail ∧
      F.R (ports (archivePorts 1 (columnBank 34))) = S.R (ports (archivePorts 1 (columnBank 34))) ∧
      ∀ j, j ≠ src → j ≠ acc → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro bank dst j rows code clean layout free input queue width blankDst savedFree tmpFree schedule
  obtain ⟨u,D,l,hu,hl,run,⟨word,after,effect⟩,freeD,stream,inputD,archive,frame⟩ :=
    queuedAnchorRecord_exec ports outside separate table g m det lift block live inputs outs result H J hm hw hW
      body v S tail rest queueTail dest q empty original layout free input queue width blankDst savedFree tmpFree schedule
  have neq := separate
  regs_ne neq
  obtain ⟨z,hz,collect,blanked⟩ := collectPayload_exec body collectPorts (SparseRoleCircuit.encode ∘ word) u D
    (by rw [(frame count ‹count ≠ src› countOff).2,width]) ((frame tmp ‹src ≠ tmp›.symm tmpOff).2.trans tmpFree)
    (fun p => by have h := (after.src p).symm; rw [sub_zero] at h; exact h)
  let F := {D with R := Function.update (Function.update D.R dst ((D.R dst).drop (M^(d+1)*W))) acc ((payloadWord (SparseRoleCircuit.encode ∘ word)).reverse ++ D.R acc)}
  have keep (i : Fin T) (ha : i ≠ acc) (hd : i ≠ dst) : F.R i = D.R i :=
    (Function.update_of_ne ha _ _).trans (Function.update_of_ne hd _ _)
  have bankKeep (i : Fin 35) (hi : i ≠ 24) := keep (ports (bank i)) (buffer _) (ports.injective.ne (bank.injective.ne hi))
  refine ⟨z,F,_,word,hz.trans hu,Nat.add_le_add_right hl _,Exec.seq run collect,effect,
    (Function.update_self ..).trans (congrArg _ (frame acc accSrc buffer).2),blanked,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨(bankKeep 2 (by decide)).trans after.modulus,(bankKeep 27 (by decide)).trans after.width,
      (bankKeep 28 (by decide)).trans after.one,(bankKeep 32 (by decide)).trans after.padded,
      (congrArg List.length (bankKeep 33 (by decide))).trans after.clock,(bankKeep 34 (by decide)).trans after.archive,
      fun i hi => ⟨(after.scratch i hi).1,(bankKeep i (fun e => (by decide : (24 : Fin 35) ∉ shearWork) (e ▸ hi))).trans (after.scratch i hi).2⟩,?_,?_⟩
    · intro p
      rw [sub_zero]
      exact (blanked p).trans ((blankDst p).symm.trans (by have e := layout.src p; rw [sub_zero] at e; exact e))
    · intro p
      change readAt blank (D.L (ports (bank 25))) (F.R (ports (bank 25))) _ = _
      rw [bankKeep 25 (by decide)]
      exact after.dst p
  · intro i hi
    refine ⟨(freeD i hi).1,(keep _ (buffer _) (ports.injective.ne ?_)).trans (freeD i hi).2⟩
    intro eq
    have e := congrArg Fin.val eq
    change i.val = 24 at e
    omega
  · apply (keep _ (buffer _) (ports.injective.ne ?_)).trans stream
    intro eq
    have e := congrArg Fin.val eq
    change rowSwapBlock.tapes+35 = 24 at e
    omega
  · exact (keep _ accSrc.symm (outside _).symm).trans inputD
  · exact (keep _ (buffer _) (ports.injective.ne (archivePorts_other 0 (columnBank 24)).symm)).trans archive
  · intro i hs ha off
    exact ⟨(frame i hs off).1,(keep i ha (off _).symm).trans (frame i hs off).2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
