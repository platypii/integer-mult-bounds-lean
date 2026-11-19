module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackQueuedResidual

/-! Execute a live record from the anchor output and pivot queues on one host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem queuedAnchorRecord_exec {r records T : ℕ} (ports : Fin (N+2) ↪ Fin T) {count src saved tmp : Fin T}
    (outside : ∀ j, ports j ≠ src)
    (separate : [count,src,ports (archivePorts 0 (columnBank 24)),saved,tmp].Nodup)
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
    ∃ z F n, z.user = v.user ∧ n ≤ 6*(M^(d+1)*W)+6+(1+signedResidualTime U rows w W H J) ∧
      Exec body (queuedResidual ports count src saved tmp d) (mk v S) n (mk z F) ∧
      ColumnReady bank H J m tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original (fun x => m.mulVec x) (embStk ports F) ∧
      clean F ∧ F.R (ports (Fin.last N).castSucc) = ((List.range records).drop (j+1)).flatMap code ++ rest ∧
      F.R src = (outs.drop (j+1)).flatMap payloadWord ++ queueTail ∧
      F.R (ports (archivePorts 1 (columnBank 34))) = S.R (ports (archivePorts 1 (columnBank 34))) ∧
      ∀ j, j ≠ src → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro bank dst j rows code clean layout free input queue width blankDst savedFree tmpFree schedule
  obtain ⟨neg,out,entry,correct,_,valid,sign⟩ := Record.output_at (by omega) table g m det lift inputs outs result block live
  obtain ⟨word,encoded,placed⟩ := Record.signedPayload neg (inputs j) out correct original input
  have same : payloadWord out = payloadWord (SparseRoleCircuit.encode ∘ word) := by
    rw [← encoded,Record.payloadWord_scalarArray]
  obtain ⟨inside,eq⟩ := List.getElem?_eq_some_iff.mp entry
  rw [show outs.drop j = out :: outs.drop (j+1) from eq ▸ (List.getElem_cons_drop inside).symm,
    List.flatMap_cons,List.append_assoc,same] at queue
  have addr := LabelStock.residue_at (by omega : 0 < w+1) block 1 0 (by decide) g
  simp only [Nat.mul_one,Nat.add_zero] at addr
  have head : code j = scheduleCode rows ++ orderedScheduleCode (List.finRange (d+1)).reverse rows := by
    simp only [code,j,addr,rows]
  have split := (List.getElem_cons_drop (show j < (List.range records).length by simpa [j] using live)).symm
  simp only [List.getElem_range] at split
  rw [split,List.flatMap_cons,head,List.append_assoc,List.append_assoc] at schedule
  let s : (ZMod M)ˣ := if neg then -1 else 1
  have sign' : (Itinerary.run rows m (d+1)).det = (s : ZMod M) := by cases neg <;> simpa [s,rows] using sign
  exact queuedResidual_exec ports outside separate rows m valid s sign' H J hm hw hW body v S tail _ _
    dest q empty original word layout free placed queue width blankDst savedFree tmpFree (by simpa only [List.append_assoc] using schedule)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
