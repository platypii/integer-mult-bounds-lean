module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryGeneratedIncoming

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
      OrdinaryRowHeaders caller w W F ∧
      (∀ z, readAt blank (F.L (caller 25)) (F.R (caller 25)) z = RadixToBinary.binaryEncoding.encode blank) ∧
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
  obtain ⟨_,stored,_⟩ := weighted
  have share (i : Fin 8) : bank (correctionColumnSlots i) = caller (correctionCallerSlots i) :=
    correctionColumnPlacement_shared caller work apart i
  have restored : OrdinaryRowHeaders caller w W F :=
    ⟨(share 0) ▸ stored.modulus,(share 3) ▸ stored.width,(share 7) ▸ stored.one,
      (share 4) ▸ stored.padded,(share 5) ▸ stored.clock⟩
  refine ⟨z,F,n,after,hu,paid.trans (Nat.add_le_add_right time _),exec,?_,?_,restored,?_,scratch,kept,other⟩
  · have port : bank 24 = caller 24 := correctionColumnPlacement_shared caller work apart 1
    intro z
    rw [← port,List.map_ofFn]
    exact (read z).symm
  · simpa only [weight,Fin.val_castAdd,Fin.isLt,dite_eq_left] using action
  · intro z
    rw [← show bank 25 = caller 25 from share 2]
    simpa only [sub_zero] using stored.dst z

open HeadPivotLayout HeadWidthLayout CrossWeightLayout GoodForm

/-- Read the parent weights and terminal pivots from the stage archive, synthesize both
child weight tapes, and return the corrected row in the outgoing adapter's layout. -/
theorem preparedDirectoryCorrection_exec [M8.Machine.Net] {P U : Type} {T r g w W : ℕ}
    (caller : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ caller j) (body : P → Pr P T columnCapacity prime U)
    (u : HS T columnCapacity prime U) (S : Stacks T prime) (dim : r+g = 64) (hW : 0 < W) :
    let m := r+g
    let M := prime^(w+1)
    let d := m+m
    let hr : r ≤ m := Nat.le_add_right ..
    let host := (Fin.castLEEmb (by decide : 57 ≤ 64)).trans caller
    let bank := adapterBank.trans (GoodChildLayout.parent.trans host)
    let headBank := head.trans bank
    let c := child.trans headBank
    ∀ (G : Matrix (Fin m) (Fin m) (ZMod M))
      (minor : ∀ k (hk : k < r), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
      (weights inv : Fin m → ZMod M) (_inverse : ∀ j, weights j * inv j = 1)
      (before : Fin (M^d*W) → ZMod 2),
    let stage := stageAt G r hr minor r le_rfl
    let pivot := fun i : Fin r => stage.M (i.castLE hr) (i.castLE hr)
    let parentWords := (List.ofFn fun i => binSyms (A := prime) M.size (weights i).val).flatten
    let packed := fun i => ordinaryChildOutput (r := r) (g := g) (w := w) before
      (ordinaryRecursivePosition r g w W (Fin.cast (ordinaryChildVolume r g w W).symm i))
    let ready := fun sign word D => HeadColumnReady (d := d) (W := W) ((coeff sign).trans headBank) (entry.trans bank)
      M.size W.size [] parentWords [] SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word D
    ready true packed S →
    S.R (c 18) = (List.ofFn fun i => binSyms M.size (pivot i).val).flatten →
    S.R (c 15) = binSyms M.size (1 : ZMod M).val → (S.R (c 16)).length = w →
    (∀ k : Fin 20, (k ≤ 14 ∧ k ≠ 4) ∨ k = 17 → S.R (c k) = []) →
    (∀ k ∈ ([55,56,58,59,61,62,63] : List (Fin 64)), S.R (caller k) = []) →
    (∀ i, S.L (work i) = [] ∧ S.R (work i) = []) →
    ∃ z F n after, z.user = u.user ∧
      n ≤ ((List.finRange r).map (fun i => childWeightTime prime w M.size i.val)).sum+1 +
        (1+(((ordinaryChildPackSchedule r g).map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1) +
          ordinaryCorrectionTime U w W M.size W.size) ∧
      Exec body ((childWeightList prime (GoodChildLayout.weights.trans host) (List.finRange r)).seq
        (directoryRowCorrection caller work apart r g)) (mk u S) n (mk z F) ∧ ready false after F ∧ OrdinaryRowHeaders caller w W F ∧
      (∀ (hg tg : Fin g → ZMod M) (x : IntegerMultBounds.Swap.Shear.State (Fin r) (ZMod M)) (j : Fin W),
        let addr := fun y => let t := childFields hg tg y; index (Fin.append t.1 t.2) j
        after (addr (Weighted.child r (fun i => weights (i.castLE hr)*pivot i)
          (fun i => inv (i.castLE hr)*Ring.inverse (pivot i)) x)) = before (addr x)) ∧
      (∀ k : Fin 64, k ≠ 55 → k ≠ 56 → (∀ i, correctionCallerSlots i ≠ k) →
        F.L (caller k) = S.L (caller k) ∧ F.R (caller k) = S.R (caller k)) := by
  intro m M d hr host bank headBank c G minor weights inv inverse before stage pivot parentWords packed ready
    initial pivots one clock scratch fresh free
  let ports := columnPorts.trans (correctionColumnPlacement caller work apart)
  let cw := pivotWeights hr weights inv inverse pivot (fun i => stage.unit _ i.isLt)
  let words := fun (f : Fin r → ZMod M) => (List.ofFn fun i => binSyms (A := prime) M.size (f i).val).flatten
  let D := {S with R := Function.update (Function.update S.R (caller 55) (words (fun i => cw i))) (caller 56) (words (fun i => (cw i).inv))}
  obtain ⟨v,t,user,time,prep⟩ := prepareGoodChild_exec body host G r hr minor weights inv inverse
    Shared50ModularControl.prime_prime M.size (Nat.lt_size_self _) u S [] []
    (by rw [List.append_nil]; exact initial.weights) (by simpa only [List.append_nil] using pivots)
    initial.modulus one clock scratch
  change Exec body _ _ _ (mk v {S with R := Function.update (Function.update S.R (caller 55)
    (words (fun i => cw i) ++ S.R (caller 55))) (caller 56) (words (fun i => (cw i).inv) ++ S.R (caller 56))}) at prep
  rw [fresh _ (by decide : (55 : Fin 64) ∈ _),fresh _ (by decide : (56 : Fin 64) ∈ _),List.append_nil,List.append_nil] at prep
  have on (k : Fin 64) (h : k ≠ 55 ∧ k ≠ 56) : D.R (caller k) = S.R (caller k) := by
    simp [D,Function.update_of_ne (caller.injective.ne h.1),Function.update_of_ne (caller.injective.ne h.2)]
  have aux (i) : D.L (work i) = [] ∧ D.R (work i) = [] := by
    simpa [D,Function.update_of_ne (apart i 55),Function.update_of_ne (apart i 56)] using free i
  have clean (k) (hk : 35 ≤ k.val) : D.L (ports k) = [] ∧ D.R (ports k) = [] := by
    have off : ¬ ∃ j, columnBank (correctionColumnSlots j) = columnPorts k := by
      rintro ⟨j,h⟩
      have val := congrArg Fin.val h
      change (correctionColumnSlots j).val = k.val at val
      omega
    have eq : ports k = work (columnPorts k) := by
      change sharedRegisterPlacement work _ correctionRole (columnPorts k) = _
      unfold sharedRegisterPlacement
      rw [show correctionRole (columnPorts k) = none from dite_eq_right off]
    rw [eq]
    exact aux _
  obtain ⟨z,F,n,after,hz,cost,run,payload,action,headers,dst,clear,kept,_⟩ :=
    directoryRowCorrection_exec caller work apart body v D dim hW cw before (by
      intro j
      change readAt blank (S.L (caller 24)) (D.R (caller 24)) _ = _
      rw [on 24 (by decide),List.map_ofFn]
      have h := (initial.src j).symm
      exact h.trans (congrArg (fun xs => RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 xs j))
        (List.ofFn_congr (ordinaryChildVolume r g w W) (SparseRoleCircuit.encode ∘
          ordinaryChildOutput (r := r) (g := g) (w := w) before ∘ ordinaryRecursivePosition r g w W)).symm))
      ⟨(on 2 (by decide)).trans initial.base,(on 53 (by decide)).trans initial.width,
       (on 28 (by decide)).trans initial.one,(on 44 (by decide)).trans one,
       (congrArg List.length (on 45 (by decide))).trans clock⟩
      (fun j => by
        rw [on 25 (by decide)]
        have h := (initial.dst j).symm
        rw [sub_zero] at h
        exact h) (fun i _ => aux _) clean
      (by exact (Function.update_of_ne (caller.injective.ne (by decide : (55 : Fin 64) ≠ 56)) ..).trans (Function.update_self ..)) (by exact Function.update_self ..)
      (fun k hk => (on k ((by decide : ∀ k ∈ ([58,59,61,62,63] : List (Fin 64)), k ≠ 55 ∧ k ≠ 56) k hk)).trans
        (fresh k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk))))
  have keep (k : Fin 64) (h : k ≠ 55 ∧ k ≠ 56 ∧ ∀ i, correctionCallerSlots i ≠ k) :=
    And.intro (kept k h.2.2).1 ((kept k h.2.2).2.trans (on k ⟨h.1,h.2.1⟩))
  refine ⟨z,F,t+n,after,hz.trans user,Nat.add_le_add time cost,Exec.seq prep run,?_,headers,action,fun k a b h => keep k ⟨a,b,h⟩⟩
  let entrySlot := fun j => (entry.trans (adapterBank.trans (GoodChildLayout.parent.trans (Fin.castLEEmb (by decide : 57 ≤ 64))))) j
  have slot (j : Fin 29) (hj : j ∈ headShearWork) := keep (entrySlot j)
    ((by decide : ∀ j ∈ headShearWork, entrySlot j ≠ 55 ∧ entrySlot j ≠ 56 ∧ ∀ i, correctionCallerSlots i ≠ entrySlot j) j hj)
  refine ⟨(keep 52 (by decide)).2.trans initial.stage,(keep 48 (by decide)).2.trans initial.weights,
    (keep 29 (by decide)).2.trans (scratch 0 (by decide)),(keep 33 (by decide)).2.trans initial.modulus,?_,
    headers.modulus,headers.one,headers.width,?_,?_,?_⟩
  · intro j hj
    let port := fun i => ((coeff false).trans (head.trans (adapterBank.trans (GoodChildLayout.parent.trans (Fin.castLEEmb (by decide : 57 ≤ 64)))))) i
    exact ((keep (port j) ((by decide : ∀ i : Fin 17, i ≤ 1 ∨ 3 ≤ i ∧ i ≤ 11 →
      port i ≠ 55 ∧ port i ≠ 56 ∧ ∀ k, correctionCallerSlots k ≠ port i) j hj)).2).trans
      (by
        have eq := (by decide : ∀ i : Fin 17, i ≤ 1 ∨ 3 ≤ i ∧ i ≤ 11 → coeff false i = coeff true i) j hj
        change S.R (headBank (coeff false j)) = []
        rw [eq]
        exact initial.coeffWork j hj)
  · intro j hj
    exact ⟨(slot j hj).1.trans (initial.scratch j hj).1,(slot j hj).2.trans (initial.scratch j hj).2⟩
  · intro j
    have h := (payload j).symm
    rw [List.map_ofFn] at h
    exact h
  · intro j
    rw [sub_zero]
    exact (dst j).symm

open Matrix M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear

/-- Complete a live returned row using the same pivot-stage archive as the incoming row. -/
theorem directoryOutgoingRow_exec [M8.Machine.Net] {P U : Type} {T r g w W : ℕ}
    (caller : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ caller j) (body : P → Pr P T columnCapacity prime U)
    (u : HS T columnCapacity prime U) (S : Stacks T prime) (dim : r+g = 64) (hW : 0 < W) :
    let m := r+g
    let M := prime^(w+1)
    let d := m+m
    let hr : r ≤ m := Nat.le_add_right ..
    let host := parentWithWeights.trans ((Fin.castLEEmb (by decide : 58 ≤ 64)).trans caller)
    let bank := adapterBank.trans (GoodChildLayout.parent.trans host)
    let headBank := head.trans bank
    let c := child.trans headBank
    ∀ (G : Matrix (Fin m) (Fin m) (ZMod M))
      (minor : ∀ k (hk : k < r), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
      (L : Matrix (Fin m) (Fin r) (ZMod M)) (R : Matrix (Fin r) (Fin m) (ZMod M))
      (_idem : G*G = G) (_factor : G = L*R)
      (weights inv : Fin m → ZMod M) (_inverse : ∀ j, weights j * inv j = 1)
      (original before : Fin (M^d*W) → ZMod 2),
    let stage := stageAt G r hr minor r le_rfl
    let pivot := fun i : Fin r => stage.M (i.castLE hr) (i.castLE hr)
    let parentWords := (List.ofFn fun i => binSyms (A := prime) M.size (weights i).val).flatten
    let packed := fun i => ordinaryChildOutput (r := r) (g := g) (w := w) before
      (ordinaryRecursivePosition r g w W (Fin.cast (ordinaryChildVolume r g w W).symm i))
    let ready := fun sign word D => HeadColumnReady (d := d) (W := W) ((coeff sign).trans headBank) (entry.trans bank)
      M.size W.size [] parentWords [] SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word D
    ready true packed S →
    S.R (c 18) = (List.ofFn fun i => binSyms M.size (pivot i).val).flatten →
    S.R (c 15) = binSyms M.size (1 : ZMod M).val → (S.R (c 16)).length = w →
    (∀ k : Fin 20, (k ≤ 14 ∧ k ≠ 4) ∨ k = 17 → S.R (c k) = []) →
    (∀ k ∈ ([55,56,58,59,61,62,63] : List (Fin 64)), S.R (caller k) = []) →
    (∀ i, S.L (work i) = [] ∧ S.R (work i) = []) →
    let words := fun j => if hj : j ≤ r then matrixWords prime M.size (stageAt G r hr minor j hj).M else []
    S.R (bank 27) = [] → S.R (caller 54) = (List.ofFn fun j => binSyms M.size (inv j).val).flatten →
    (S.R (headBank 49),S.R (headBank 50)) = matrixArchive words (words 0) [] r →
    (S.R (headBank 51)).length = m*m*M.size →
    IncomingRowEffect (w := w) (W := W) hr G minor weights inv original before →
    let machine := GoodChildLayout.parent.trans host
    let cap : 217 ≤ columnCapacity := le_max_left ..
    let exit := (stateLiftNormalize cap (by decide)).seq (stateLiftPr cap (by decide) Empty.elim (goodOutgoing prime r hr machine))
    let prepare := (childWeightList prime (GoodChildLayout.weights.trans host) (List.finRange r)).seq
      (directoryRowCorrection caller work apart r g)
    ∃ z F n out, z.user = u.user ∧
      n ≤ (((List.finRange r).map (fun i => childWeightTime prime w M.size i.val)).sum+1 +
        (1+(((ordinaryChildPackSchedule r g).map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1) +
          ordinaryCorrectionTime U w W M.size W.size)) +
        (1+goodOutgoingTime (A := prime) (U := U) Empty.elim machine prime w W M.size W.size r hr) ∧
      Exec body (prepare.seq exit) (mk u S) n (mk z F) ∧ RecordPayload (caller 24) (fun _ => blank) 0 out F ∧
      (∀ x j, let y := transform (diagonal weights) 1 (revExchangeOf (rev m) G (transform (diagonal inv) 1 x))
        out (index (Fin.append y.1 y.2) j) = original (index (Fin.append x.1 x.2) j)) ∧
      OrdinaryRowHeaders caller w W F ∧
      ∀ k : Fin 64, 29 ≤ k.val → k ≠ 55 → k ≠ 56 → (∀ i, correctionCallerSlots i ≠ k) →
        F.R (caller k) = S.R (caller k) := by
  intro m M d hr host bank headBank c G minor L R idem factor weights inv inverse original before stage pivot parentWords
    packed ready initial pivots one clock scratch fresh free words empty inverses archive count inc machine cap exit prepare
  obtain ⟨v,D,t,after,user,time,first,position,headers,childAction,keep⟩ := preparedDirectoryCorrection_exec caller work apart
    body u S dim hW G minor weights inv inverse before initial pivots one clock scratch fresh free
  have kept (k : Fin 64) (hk : k ≠ 55 ∧ k ≠ 56 ∧ ∀ i, correctionCallerSlots i ≠ k) :=
    (keep k hk.1 hk.2.1 hk.2.2).2
  obtain ⟨y,F,n,out,hy,cost,last,done,blankPort,frame,action⟩ := goodOutgoing_exec (P := Empty) Empty.elim machine
    G r hr minor idem L R factor weights inv inverse Shared50ModularControl.prime_prime M.size W.size
    (Nat.lt_size_self _) (Nat.lt_size_self _) hW [] [] [] [] [] SparseRoleCircuit.encode
    (fun _ => blank) (fun _ => blank) 0 0 (fun _ _ _ => rfl) (stateLiftDown (by decide : 0 < 217) v) D _
    (by rw [List.append_nil]; exact position) ((kept 27 (by decide)).trans empty)
    (by rw [List.append_nil]; exact (kept 54 (by decide)).trans inverses)
    (by rw [List.append_nil]; exact (congrArg₂ Prod.mk (kept 49 (by decide)) (kept 50 (by decide))).trans archive)
    ((congrArg List.length (kept 51 (by decide))).trans count)
    (by rw [List.append_nil]; exact (kept 47 (by decide)).trans pivots) headers.padded headers.clock (by
      intro j hj
      let k := (child.trans (head.trans (adapterBank.trans (GoodChildLayout.parent.trans (Fin.castLEEmb (by decide : 57 ≤ 64)))))) j
      exact (kept k ((by decide : ∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 →
        let k := (child.trans (head.trans (adapterBank.trans (GoodChildLayout.parent.trans (Fin.castLEEmb (by decide : 57 ≤ 64)))))) j
        k ≠ 55 ∧ k ≠ 56 ∧ ∀ i, correctionCallerSlots i ≠ k) j hj)).trans (scratch j hj))
  have held (k : Fin 64) (hk : 29 ≤ k.val) (off : k ≠ 53) : F.R (caller k) = D.R (caller k) := by
    let small := GoodChildLayout.parent.trans (Fin.castLEEmb (by decide : 57 ≤ 64))
    exact (frame _ (fun i => caller.injective.ne ((by decide : ∀ i (k : Fin 64), 29 ≤ k.val → k ≠ 53 →
      small (adapterBank (head (shear i))) ≠ k) i k hk off)) (fun i => caller.injective.ne
      ((by decide : ∀ i (k : Fin 64), 29 ≤ k.val → k ≠ 53 → small (adapterBank (ordinaryHead (shear i))) ≠ k) i k hk off))).2
  refine ⟨stateLiftUp cap y,F,_,out,hy.trans user,Nat.add_le_add time (Nat.add_le_add_left cost 1),
    Exec.seq first (stateLift_exec_normalized cap (by decide) Empty.elim (body' := body) (fun f => nomatch f) v last),?_,
    goodRecord_effect stage L R factor idem weights inv inverse original before _ out inc childAction action,
    ⟨done.base,done.width,done.one,(held 44 (by decide) (by decide)).trans headers.padded,
      (congrArg List.length (held 45 (by decide) (by decide))).trans headers.clock⟩,?_⟩
  · intro j
    rw [List.map_ofFn]
    exact (done.src j).symm
  · intro k hk a b off
    exact (held k hk (off 3).symm).trans (kept k ⟨a,b,off⟩)

open LabelTraversal IntegerMultBounds.Swap.Modular

/-- Regenerate the outgoing stage from the label directory and execute its weighted
correction and coordinate transform on a live ordinary row. -/
theorem generatedLiveOutgoingRow_exec [M8.Machine.Net] {P U : Type} {r g w W common work : ℕ}
    (v : RecursiveInterchangeLayout.Descriptor) :
    let m := r+g
    let hr : r ≤ m := Nat.le_add_right ..
    let K := common+24+31+work
    let M := prime^(w+1)
    let H := M.size
    let J := W.size
    ∀ (proj : Matrix (Fin m) (Fin m) ℚ) (_rank : proj.rank = r) (_dim : m = 64)
      (weights : Fin m → ZMod M) (_unit : ∀ i, IsUnit (weights i))
      (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
      (schedules : List ℕ → List (Fin (prime+4))) (j : ℕ) (js : List ℕ)
      (pool : (RingFormula.conjugationDepth m+1)*13 ≤ work) (room : 58+(rowSwapBlock.tapes+35+1) ≤ K)
      (body : P → Pr P (66+K) columnCapacity prime U) (u : HS (66+K) columnCapacity prime U) (S : Stacks (66+K) prime),
    let full := ordinaryCaller (by omega : 58 ≤ K)
    let bank := ordinaryPackingBank (by omega : 58 ≤ K)
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let label := physicalLabel m (w+1) j
    let reduced := reduce M proj
    let G := label*reduced*label⁻¹
    let inv := fun i => Ring.inverse (weights i)
    let setup := ordinaryRowSetup (P := P) (U := U) (common := common) r g pool (by omega)
    let write := childWeightList prime (GoodChildLayout.weights.trans (parentWithWeights.trans full)) (List.finRange r)
    let corr := directoryRowCorrection bank (ordinaryPackingWork room) (ordinaryPackingWork_apart room) r g
    let cap : 217 ≤ columnCapacity := le_max_left ..
    let exit := (stateLiftNormalize cap (by decide)).seq (stateLiftPr cap (by decide) Empty.elim (goodOutgoing prime r hr machine))
    proj*proj = proj → ∀ f : IntegerMultBounds.Swap.LowerTriangular.Factorization Finset.univ Finset.univ proj,
    (∀ k ∈ factorizationDenominators f, k < prime) →
    DirectoryReady v proj w W H J weights prefixes tail schedules S (j::js) →
    LabelStock.live m (w+1) 1 j = true → fallbackBit proj.rank_le_height reduced label = false → 0 < W →
    ∀ (original before : Fin (M^(m+m)*W) → ZMod 2)
      (minor : ∀ k (hk : k < r), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det),
    IncomingRowEffect (w := w) (W := W) hr G minor weights inv original before →
    let pos := ordinaryRecursivePosition r g w W
    let plain := ordinaryChildOutput (r := r) (g := g) (w := w) before
    RecordPayload (full 24) (fun _ => blank) 0 (plain ∘ pos) S →
    ∃ z F n out, z.user = u.user ∧
      n ≤ ordinarySetupTime m r w H (prefixes j).length +
        ((((List.finRange r).map (fun i => childWeightTime prime w H i.val)).sum+1 +
          (1+(((ordinaryChildPackSchedule r g).map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim (m+m) i (i+1) w W H J)).sum+1) +
            ordinaryCorrectionTime U w W H J)) + (1+goodOutgoingTime (A := prime) (U := U) Empty.elim machine prime w W H J r hr)) ∧
      Exec body (setup.seq ((write.seq corr).seq exit)) (mk u S) n (mk z F) ∧
      RecordPayload (full 24) (fun _ => blank) 0 out F ∧
      (∀ x k, let y := transform (diagonal weights) 1 (revExchangeOf (rev m) G (transform (diagonal inv) 1 x))
        out (index (Fin.append y.1 y.2) k) = original (index (Fin.append x.1 x.2) k)) ∧
      OrdinaryRowHeaders bank w W F := by
  intro m hr K M H J proj rank dim weights unit prefixes tail schedules j js pool room body u S full bank
    machine label reduced G inv setup write corr cap exit idemProj f small ready live regular hW original before minor inc pos plain payload
  obtain ⟨_,idem,factors⟩ := physicalGood_inputs (by omega : 0 < w+1) proj idemProj f small proj.rank_le_height j live regular
  rw [rank] at factors
  obtain ⟨L,R,factor⟩ := factors
  let packed := fun i : Fin (M^(m+m)*W) => plain (pos (i.cast (ordinaryChildVolume r g w W).symm))
  have generated := ordinaryGeneratedSetup_exec (common := common) (work := work) (H := H) (J := J) v proj weights
    prefixes tail schedules (Nat.lt_size_self _) pool unit (by omega : 58 ≤ K) body u S j js ready live regular packed (by
      intro k
      have h := (payload k).symm
      rw [sub_zero,List.map_ofFn] at h
      change _ = readAt blank (S.L (full 24)) (S.R (full 24)) k
      exact (congrArg (fun xs => RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 xs k))
        (List.ofFn_congr (ordinaryChildVolume r g w W) (SparseRoleCircuit.encode ∘ plain ∘ pos)).symm).trans h)
  simp only [rank] at generated
  obtain ⟨_,a,A,t,ha,ht,prepare,initial,empty,one,clock,scratch,temps,extra,inverses,count,pivots,pair,publicFrame⟩ := generated
  have privateFree := ready.2.2.1
  have fresh : ∀ k ∈ ([55,56,58,59,61,62,63] : List (Fin 64)), A.R (bank k) = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with h|h|h|h|h|h|h <;> subst k
    · exact temps _ (List.mem_cons_self ..)
    · exact temps _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    all_goals exact (publicFrame _ (by change (ordinaryPackingSlot _).val < 66; decide)).trans (privateFree _ (by change 58 ≤ (ordinaryPackingSlot _).val; decide)).2
  have pass := directoryOutgoingRow_exec (w := w) bank (ordinaryPackingWork room) (ordinaryPackingWork_apart room) body a A dim hW
  dsimp only at pass
  rw [ordinaryPackingBank_entry] at pass
  obtain ⟨z,F,n,out,hz,time,run,read,action,headers,_⟩ := pass G minor L R idem factor weights inv
    (fun i => Ring.mul_inverse_cancel _ (unit i)) original before initial (pivots.trans (pivotWords_cast G hr minor rank H))
    one clock scratch fresh (fun i => extra _ (by change 124 ≤ 124+i.val; omega)) empty inverses pair count inc
  exact ⟨z,F,t+n,out,hz.trans ha,Nat.add_le_add ht time,Exec.seq prepare run,read,action,headers⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
