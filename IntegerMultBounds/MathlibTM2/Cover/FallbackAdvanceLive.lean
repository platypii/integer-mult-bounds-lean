module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackNextRecord
public import IntegerMultBounds.MathlibTM2.Cover.FallbackMaskedScan

/-! Execute and collect one live record, then advance its matrix archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

open Mult.ShortConv

/-- Both branches advance the matrix archive once per mask bit. -/
noncomputable def residualScan {T : ℕ} (ports : Fin (N+2) ↪ Fin T) (mask count src saved tmp acc : Fin T)
    (d : ℕ) : Pr P T columnCapacity prime U :=
  let bank := (columnBank.trans (archivePorts 0)).trans ports
  let advance := dropWords (bank 2) (bank 34) (bank 0) ((d+1)*(d+1))
  let live := collectAnchorRecord ports count src saved tmp acc d
  let padding := paddingRecord (d+1) (ports (Fin.last N).castSucc) count src acc tmp
  maskedScan mask (.seq live advance) (.seq padding advance)

theorem advanceLive_exec {r records T : ℕ} (ports : Fin (N+2) ↪ Fin T) {count src saved tmp acc : Fin T}
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
    ∃ z F n word, z.user = v.user ∧ n ≤ 6*(M^(d+1)*W)+6+(1+signedResidualTime U rows w W H J)+(4*(M^(d+1)*W)+4)+((d+1)*(d+1)*(4*H+4)+1) ∧
      Exec body (.seq (collectAnchorRecord ports count src saved tmp acc d)
        (dropWords (ports (bank 2)) (ports (bank 34)) (ports (bank 0)) ((d+1)*(d+1)))) (mk v S) n (mk z F) ∧
      (∀ x k, word (FlatCoordinateLayout.index (m.mulVec x) k) = original (FlatCoordinateLayout.index x k)) ∧
      F.R acc = (payloadWord (SparseRoleCircuit.encode ∘ word)).reverse ++ S.R acc ∧
      (∀ z, readAt blank (F.L dst) (F.R dst) z = blank) ∧
      F.R (ports (bank 34)) = tail ∧
      (∀ next rest (input : Fin (M^(d+1)*W) → ZMod 2), tail = matrixWords prime H next ++ rest →
        ShearReady bank H J next rest (fun _ : ZMod 2 => blank) (fun _ => blank) dest 0 q input (embStk ports F)) ∧
      clean F ∧ F.R (ports (Fin.last N).castSucc) = ((List.range records).drop (j+1)).flatMap code ++ rest ∧
      F.R src = (outs.drop (j+1)).flatMap payloadWord ++ queueTail ∧
      F.R (ports (archivePorts 1 (columnBank 34))) = S.R (ports (archivePorts 1 (columnBank 34))) ∧
      ∀ j, j ≠ src → j ≠ acc → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro bank dst j rows code clean layout free input queue width blankDst savedFree tmpFree schedule
  obtain ⟨u,D,l,word,hu,hl,run,act,output,blanked,ready,cleanD,pivots,words,archive,frame⟩ :=
    collectAnchorRecord_exec ports outside separate collectPorts buffer countOff tmpOff accSrc table g m det lift block live
      inputs outs result H J hm hw hW body v S tail rest queueTail dest q empty original layout free input queue width
      blankDst savedFree tmpFree schedule
  let tapes := bank.trans ports
  obtain ⟨z,hz,advance⟩ := consumeMatrix_exec tapes body u D H m tail ready.archive
    ((congrArg List.length ready.modulus).trans (length_binSyms ..)) (ready.scratch 0 (by decide)).2
  let F := {D with R := Function.update D.R (tapes 34) tail}
  have keep (i : Fin T) (hi : i ≠ tapes 34) : F.R i = D.R i := Function.update_of_ne hi _ _
  refine ⟨z,F,_,word,hz.trans hu,Nat.add_le_add_right hl _,.seq run advance,act,
    (keep _ (buffer _).symm).trans output,?_,Function.update_self ..,?_,?_,?_,(keep _ (outside _).symm).trans words,?_,?_⟩
  · simpa only [show F.R dst = D.R dst from keep _ (tapes.injective.ne (by decide : (24 : Fin 35) ≠ 34))] using blanked
  · intro next rest input eq
    have h : F.R (tapes 34) = tail := Function.update_self ..
    apply ready.next (F := embStk ports F) (nextWord := input) (h.trans eq) (fun _ => rfl)
    · intro i hi
      exact keep _ (tapes.injective.ne hi)
    · rfl
  · intro i hi
    refine ⟨(cleanD i hi).1,(keep _ (ports.injective.ne ?_)).trans (cleanD i hi).2⟩
    intro eq
    have e := congrArg Fin.val eq
    change i.val = 34 at e
    omega
  · apply (keep _ (ports.injective.ne ?_)).trans pivots
    intro eq
    have e := congrArg Fin.val eq
    change rowSwapBlock.tapes+35 = 34 at e
    omega
  · exact (keep _ (ports.injective.ne (archivePorts_other 0 (columnBank 34)).symm)).trans archive
  · intro i hs ha off
    exact ⟨(frame i hs ha off).1,(keep _ (off _).symm).trans (frame i hs ha off).2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
