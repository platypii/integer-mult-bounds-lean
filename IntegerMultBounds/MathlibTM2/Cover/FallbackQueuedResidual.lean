module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSignedResidual
public import IntegerMultBounds.MathlibTM2.Cover.FallbackAnchorLayout

/-! Load and execute a signed payload while retaining the unread record queue. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

open Mult.PhaseCellToeplitz

noncomputable def queuedResidual {T : ℕ} (ports : Fin (N+2) ↪ Fin T) (count src saved tmp : Fin T) (d : ℕ) :
    Pr P T columnCapacity prime U :=
  .seq (movePrefix count src (ports (archivePorts 0 (columnBank 24))) saved tmp)
    (statePlacedNormalized ports le_rfl (lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..))
      Empty.elim (signedResidual d))

theorem queuedResidual_exec {T : ℕ} (ports : Fin (N+2) ↪ Fin T) {count src saved tmp : Fin T}
    (outside : ∀ j, ports j ≠ src)
    (separate : [count,src,ports (archivePorts 0 (columnBank 24)),saved,tmp].Nodup)
    (rows : Fin (d+1) → Fin (d+1)) (m : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    (valid : Itinerary.Valid rows m (d+1)) (s : (ZMod M)ˣ) (sign : (Itinerary.run rows m (d+1)).det = (s : ZMod M))
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P T columnCapacity prime U) (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (tail rest queueTail : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original word : Fin (M^(d+1)*W) → ZMod 2) :
    let bank := columnBank.trans (archivePorts 0)
    let dst := ports (bank 24)
    let anchor := fun x j => ((Fin.cons s (fun _ => 1) : Fin (d+1) → (ZMod M)ˣ) j : ZMod M) * x j
    let clean := fun (D : Stacks T prime) => ∀ i : Fin N, 35 ≤ i.val →
      D.L (ports (columnPorts i).castSucc) = [] ∧ D.R (ports (columnPorts i).castSucc) = []
    ShearReady bank H J m tail (fun _ : ZMod 2 => blank) (fun _ => blank) dest 0 q original (embStk ports S) →
    clean S → (∀ x j, word (FlatCoordinateLayout.index (anchor x) j) = original (FlatCoordinateLayout.index x j)) →
    S.R src = payloadWord (SparseRoleCircuit.encode ∘ word) ++ queueTail → (S.R count).length = M^(d+1)*W →
    (∀ z, readAt blank (S.L dst) (S.R dst) z = blank) → S.R saved = [] → S.R tmp = [] →
    S.R (ports (Fin.last N).castSucc) = scheduleCode rows ++ orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest →
    ∃ z F n, z.user = v.user ∧ n ≤ 6*(M^(d+1)*W)+6+(1+signedResidualTime U rows w W H J) ∧
      Exec body (queuedResidual ports count src saved tmp d) (mk v S) n (mk z F) ∧
      ColumnReady bank H J m tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original (fun x => m.mulVec x) (embStk ports F) ∧
      clean F ∧ F.R (ports (Fin.last N).castSucc) = rest ∧ F.R src = queueTail ∧
      F.R (ports (archivePorts 1 (columnBank 34))) = S.R (ports (archivePorts 1 (columnBank 34))) ∧
      F.L src = S.L src ∧
      ∀ j, j ≠ src → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro bank dst anchor clean layout free placed queue width blankDst savedFree tmpFree code
  obtain ⟨u,D,hu,load,stateEq,tape⟩ := loadPayload_exec body separate (SparseRoleCircuit.encode ∘ word)
    queueTail v S queue width blankDst savedFree tmpFree
  have keep (j : Fin (N+2)) (hj : j ≠ bank 24) : D.R (ports j) = S.R (ports j) := by
    rw [stateEq]; exact (Function.update_of_ne (ports.injective.ne hj) _ _).trans (Function.update_of_ne (outside j) _ _)
  have bankKeep (j : Fin 35) (hj : j ≠ 24) := keep _ (bank.injective.ne hj)
  have left : D.L = S.L := by rw [stateEq]
  have ready : ColumnReady bank H J m tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original anchor (embStk ports D) := by
    refine ⟨word,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,placed⟩
    · exact (bankKeep 2 (by decide)).trans layout.modulus
    · exact (bankKeep 27 (by decide)).trans layout.width
    · exact (bankKeep 28 (by decide)).trans layout.one
    · exact (bankKeep 32 (by decide)).trans layout.padded
    · exact (congrArg List.length (bankKeep 33 (by decide))).trans layout.clock
    · exact (bankKeep 34 (by decide)).trans layout.archive
    · intro j hj
      exact ⟨by simpa only [embStk_L,left] using (layout.scratch j hj).1,
        (bankKeep j (fun e => (by decide : (24 : Fin 35) ∉ shearWork) (e ▸ hj))).trans (layout.scratch j hj).2⟩
    · intro z
      rw [sub_zero]; exact (tape z).symm
    · intro z
      simpa only [embStk_L,embStk_R,left,bankKeep 25 (by decide)] using layout.dst z
  have freeD : clean D := by
    intro j hj
    refine ⟨by rw [left]; exact (free j hj).1,(keep _ ?_).trans (free j hj).2⟩
    intro eq
    have h := congrArg Fin.val eq
    change j.val = 24 at h
    omega
  have stream := (keep (Fin.last N).castSucc (by
    intro eq
    have h := congrArg Fin.val eq
    change rowSwapBlock.tapes+35 = 24 at h
    omega)).trans code
  let positive : 0 < columnCapacity := lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..)
  obtain ⟨y,E,n,hy,hn,run,next,freeE,endStream,archive⟩ := signedResidual_exec rows m valid s sign H J hm hw hW
    (P := Empty) Empty.elim (stateLiftDown positive (embDn ports u)) (embStk ports D)
    tail rest dest q empty original ready freeD (by simpa only [embStk_R,List.append_assoc] using stream)
  obtain ⟨z,_,hz,finish⟩ := statePlaced_exec_normalized ports ports.injective le_rfl positive Empty.elim
    (body' := body) (fun e => nomatch e) u D run
  let F := embOvr ports E.get D
  have eq : embStk ports F = E := embStk_ovr ports.injective _ _
  rw [← eq] at next freeE endStream archive
  refine ⟨z,F,_,hz.trans (hy.trans hu),Nat.add_le_add_left (Nat.add_le_add_left hn 1) _,Exec.seq load finish,
    next,freeE,endStream,(embOvr_off _ D outside).2.trans ?_,archive.trans (keep _ ?_),(embOvr_off _ D outside).1.trans (congrFun left src),?_⟩
  · rw [stateEq]; exact (Function.update_of_ne (outside (bank 24)).symm _ _).trans (Function.update_self ..)
  · exact (archivePorts_other 0 (columnBank 24)).symm
  · intro j hsrc off
    have untouched := embOvr_off E.get D off
    refine ⟨untouched.1.trans (congrFun left j),untouched.2.trans ?_⟩
    rw [stateEq]
    exact (Function.update_of_ne (off (bank 24)).symm _ _).trans (Function.update_of_ne hsrc _ _)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
