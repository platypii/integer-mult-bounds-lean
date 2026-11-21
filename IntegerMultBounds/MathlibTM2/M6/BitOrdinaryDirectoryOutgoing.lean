module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIncoming

/-! Unpack a live row returned by the shared transpose and apply its pivot correction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open GoodChildLayout FlatCoordinateLayout
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Reverse the packing pass, then synthesize and apply the diagonal correction. -/
noncomputable def directoryRowCorrection [M8.Machine.Net] {P U : Type} {T : ℕ}
    (caller : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ caller j) (r g : ℕ) : Pr P T columnCapacity prime U :=
    let d := (r+g)+(r+g)
    let is := ordinaryChildPackSchedule r g
    let placement := correctionColumnPlacement caller work apart
    let ports := columnPorts.trans placement
    let bank := columnBank.trans placement
    let unpack : Pr P T columnCapacity prime U :=
      statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule d is.reverse)
    let emit := fun i j => let slot := correctionSlot r i j
                           readMatrixWord slot.2.val ((callerCorrectionPorts slot.1).trans caller)
    let write := LabelTraversal.sequence (fun i => LabelTraversal.sequence (emit i) (List.finRange 128)) (List.finRange 128)
    let prep := (bzero (caller 2) (caller 58) (caller 59)).seq (write.seq (bclear (caller 58)))
    let correction := (prep.seq (placedDiagonalPairs placement 127)).seq (dropWords (bank 2) (bank 34) (bank 0) (128*128))
    unpack.seq correction

theorem directoryRowCorrection_exec [M8.Machine.Net] {P U : Type} {T r g w W : ℕ}
    (caller : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ caller j) (body : P → Pr P T columnCapacity prime U)
    (u : HS T columnCapacity prime U) (S : Stacks T prime) (dim : r+g = 64) (hW : 0 < W)
    (pivot : Fin r → (ZMod (prime^(w+1)))ˣ) :
    let m := r+g
    let d := m+m
    let M := prime^(w+1)
    let placement := correctionColumnPlacement caller work apart
    let ports := columnPorts.trans placement
    let is := ordinaryChildPackSchedule r g
    let clean := fun D : Stacks T prime => ∀ i, 35 ≤ i.val → D.L (ports i) = [] ∧ D.R (ports i) = []
    ∀ before : Fin (M^d*W) → ZMod 2,
    let plain := ordinaryChildOutput (r := r) (g := g) (w := w) before
    RecordPayload (caller 24) (fun _ => blank) 0 (plain ∘ ordinaryRecursivePosition r g w W) S →
    OrdinaryRowHeaders caller w W S →
    (∀ z, readAt blank (S.L (caller 25)) (S.R (caller 25)) z = RadixToBinary.binaryEncoding.encode blank) →
    (∀ i ∈ shearWork, S.L (work (columnBank i)) = [] ∧ S.R (work (columnBank i)) = []) → clean S →
    S.R (caller 55) = (List.ofFn fun i => binSyms M.size (pivot i : ZMod M).val).flatten →
    S.R (caller 56) = (List.ofFn fun i => binSyms M.size (pivot i).inv.val).flatten →
    (∀ k ∈ ([58,59,61,62,63] : List (Fin 64)), S.R (caller k) = []) →
    ∃ z F n after, z.user = u.user ∧
      n ≤ 1+((is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1) +
        ordinaryCorrectionTime U w W M.size W.size ∧
      Exec body (directoryRowCorrection caller work apart r g) (mk u S) n (mk z F) ∧
      RecordPayload (caller 24) (fun _ => blank) 0 after F ∧
      (∀ (hg tg : Fin g → ZMod M) (x : IntegerMultBounds.Swap.Shear.State (Fin r) (ZMod M)) (j : Fin W),
        let addr := fun y => let t := childFields hg tg y; index (Fin.append t.1 t.2) j
        after (addr (Weighted.child r (fun k => (pivot k : ZMod M)) (fun k => (pivot k).inv) x)) = before (addr x)) ∧
      clean F ∧ (∀ j : Fin 64, (∀ k, correctionCallerSlots k ≠ j) → F.L (caller j) = S.L (caller j) ∧ F.R (caller j) = S.R (caller j)) ∧
      ∀ j, (∀ k, placement k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro m d M placement ports is clean before plain payload headers dst temps free pos inv fresh
  let bank := columnBank.trans placement
  let row := plain ∘ ordinaryRecursivePosition r g w W
  let size := ordinaryChildVolume r g w W
  have layout := correctionRecordEntry caller work apart M.size W.size d (fun _ => blank) 0 S
    (fun i => row (i.cast size.symm)) headers.modulus headers.width headers.one headers.padded headers.clock temps
    (by
      intro z
      have h := payload z
      rw [List.map_ofFn] at h
      exact h.trans (congrArg (fun xs => RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 xs z)) (List.ofFn_congr size (SparseRoleCircuit.encode ∘ row)))) (by simpa using dst)
  obtain ⟨v,D,t,user,time,run,done,clear,frame⟩ := ordinaryOutgoingUnpack_exec ports body u S _ (fun _ => blank) 0 hW plain layout free
  let input := fun x : Fin d → ZMod M => (fun k : Fin m => x (k.castAdd m),fun k : Fin m => x (k.natAdd m))
  have ready : ColumnRecordReady bank M.size W.size (S.R (caller 60)) SparseRoleCircuit.encode (fun _ => blank)
      (fun _ => blank) 0 0 before (fun x => let s := Weighted.child r (fun _ => 1) (fun _ => 1) (input x)
                                            Fin.append s.1 s.2) D := by
    refine ⟨plain,done,?_⟩
    intro x j
    apply Eq.trans _ (congrArg (fun y => before (index y j)) (Fin.append_castAdd_natAdd (f := x)))
    apply goodChild_effect (fun _ => 1) (fun _ => 1) before plain
    intro hg tg s k
    have cell := ordinaryRecursiveTranspose_read before plain ((ordinaryChildOutput_eq_iff ..).1 rfl)
      hg tg s.1 (fun i => s.2 i.rev) k
    simpa only [Weighted.child,Fin.isLt,ite_true,one_mul,Fin.rev_rev] using cell
  obtain ⟨z,F,n,hu,paid,exec,weighted,scratch,_,kept,other,_⟩ :=
    dispatchedCorrection_exec caller work apart dim (Nat.le_add_right r g) pivot M.size W.size
      (Nat.lt_size_self _) (Nat.lt_size_self _) hW body u S _ v D t _ (fun _ => blank) 0
      (fun _ _ _ => rfl) before input pos inv fresh user run frame ready clear
  let weight := fun k : Fin m => if h : k.val < r then pivot ⟨k.val,h⟩ else 1
  obtain ⟨after,action,read⟩ := weightedColumn_return bank M.size W.size _ (fun _ => blank) 0 F before
    (fun k => (weight k : ZMod M)) (fun k => (weight k).inv) weighted
  refine ⟨z,F,n,after,hu,paid.trans (Nat.add_le_add_right time _),exec,?_,?_,scratch,kept,other⟩
  · have port : bank 24 = caller 24 := correctionColumnPlacement_shared caller work apart 1
    intro z
    rw [← port,List.map_ofFn]
    exact (read z).symm
  · simpa only [weight,Fin.val_castAdd,Fin.isLt,dite_eq_left] using action

end IntegerMultBounds.MathlibTM2.M6.BitNode
