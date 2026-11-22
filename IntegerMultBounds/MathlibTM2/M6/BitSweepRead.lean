module

public import IntegerMultBounds.MathlibTM2.M6.BitNineStageHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderStagedExchange

/-! Logical reads from the collapsed PR589 sweep output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine Swap.Modular
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- After the sweep releases its scratch owner, every inactive role still
carries the family exchange in the chart of its certified port. -/
theorem sweepEffect_inactive {n : Fin 9} {w B W : ℕ} {x y : OwnerArray w B W}
    (step : sweepEffect n w B W x y) (r : Role) (inactive : r.bank.val / 2 ≠ BitHosting.activePair n.val)
    (b : Fin B) (j : Fin W) :
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role r)).castSucc
    let addr := fun s =>
      let digits := helperSlotField (port r.port.val) none w s
      finProdFinEquiv (FlatCoordinateLayout.rank (digits ∘ Fin.castAdd 112),
        finProdFinEquiv (b,finProdFinEquiv (FlatCoordinateLayout.rank (digits ∘ Fin.natAdd 16),j)))
    ∀ s, y tape (addr (M8.Exchange.exchange (reduce (prime^w) (familySum n r)) s)) = x tape (addr s) := by
  intro tape addr s
  obtain ⟨packed,out,⟨trace,restore⟩,rfl⟩ := step
  rw [Function.update_of_ne (Fin.castSucc_ne_last _)]
  let label := firstRowLabel w
  let K := (prime^w)^112*W
  let z : LabelEntry.Cell (copyLabelLayout w B K) B :=
    ⟨⟨0,pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _⟩,⟨0,Nat.zero_lt_one⟩,b,
      ⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,⟨0,Nat.zero_lt_one⟩,
      ⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,
      finProdFinEquiv (FlatCoordinateLayout.rank (helperSlotField (port r.port.val) none w s ∘ Fin.natAdd 16),j)⟩
  have read := restoredStage_inactiveRow n w B W label x packed out trace restore r inactive label z j s
  have supported := restoredStage_inactiveWord n w B W label x packed out trace restore r inactive
  dsimp only at read supported
  rw [supported,singleLabelBank_helperCell] at read
  simpa only [Fin.val_cast,ite_true] using read

/-- Decode a staged owner cell into its unique inherited block, coordinate
vector and spectator. The forward map is the scanner's ordinary address. -/
def stagedCoordinateEquiv (M B W : ℕ) [NeZero M] :
    Fin B × ((Fin 128 → ZMod M) × Fin W) ≃ Fin (M^16*(B*(M^112*W))) where
  toFun := fun (b,x,k) => stagedOwnerIndex b (FlatCoordinateLayout.index x k)
  invFun := fun i =>
    let (a,t) := finProdFinEquiv.symm i
    let (b,v) := finProdFinEquiv.symm t
    let j := (finProdFinEquiv (a,v)).cast (ordinaryCompact_width M W)
    let (r,k) := finProdFinEquiv.symm j
    (b,FlatCoordinateLayout.coordinates r,k)
  left_inv := by
    rintro ⟨b,x,k⟩
    simp only [stagedOwnerIndex,FlatCoordinateLayout.index,Equiv.symm_apply_apply,
      Prod.mk.eta,Equiv.apply_symm_apply,Fin.cast_cast,Fin.cast_refl,id_eq,
      FlatCoordinateLayout.coordinates_rank]
  right_inv := by
    intro i
    simp only [stagedOwnerIndex,FlatCoordinateLayout.index,Equiv.symm_apply_apply,
      Prod.mk.eta,Equiv.apply_symm_apply,Fin.cast_cast,Fin.cast_refl,id_eq,
      FlatCoordinateLayout.rank_coordinates]

/-- The sweep and scanner store the inherited block at the same split
between active and spectator digits. -/
theorem stagedOwnerIndex_index {M B W : ℕ} [NeZero M] (digits : Fin 128 → ZMod M)
    (b : Fin B) (j : Fin W) :
    stagedOwnerIndex b (FlatCoordinateLayout.index digits j) =
      finProdFinEquiv (FlatCoordinateLayout.rank (digits ∘ Fin.castAdd 112),
        finProdFinEquiv (b,finProdFinEquiv (FlatCoordinateLayout.rank (digits ∘ Fin.natAdd 16),j))) := by
  let live := digits ∘ Fin.castAdd 112
  let tail : Fin 112 → ZMod M := digits ∘ Fin.natAdd 16
  have rank := ArbitraryWidthSliceTranspose.rank_append live tail
  have joined : (fun i => Fin.addCases live tail i) = digits := by
    funext i
    induction i using Fin.addCases (m := 16) (n := 112) <;> simp [live,tail]
  rw [joined] at rank
  have split : (FlatCoordinateLayout.index digits j).cast (ordinaryCompact_width M W).symm =
      finProdFinEquiv (FlatCoordinateLayout.rank live,finProdFinEquiv (FlatCoordinateLayout.rank tail,j)) := by
    apply Fin.ext
    simp only [Fin.val_cast,FlatCoordinateLayout.index_val,rank,finProdFinEquiv_apply_val]
    ring
  simp only [stagedOwnerIndex,split,Equiv.symm_apply_apply,live,tail]

/-- Read a logical address in the entry chart for its port. The eight banks
of a replica, port and class use the same address. -/
noncomputable def sweepAddress {w B W : ℕ} (b : Fin B) (j : Fin W) (lane : BankLane)
    (z : Axis ⊕ Axis → ℚ) : Fin ((prime^w)^16*(B*((prime^w)^112*W))) :=
  let v := addressMod (prime^w) z
  let digits := helperSlotField (port lane.2.1.val) none w (v ∘ Sum.inl,v ∘ Sum.inr)
  stagedOwnerIndex b (FlatCoordinateLayout.index digits j)

open Matrix in
/-- Change the node's weighted and reversed fields into the common port
chart used by the two halves of an inactive sweep. -/
theorem sweepAddress_from_parent {w B W : ℕ} (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (b : Fin B) (j : Fin W) (lane : BankLane) (z : Axis ⊕ Axis → ℚ) :
    let c := port lane.2.1.val
    let H := (reduce (prime^w) (c.fullChart.submatrix stageAxis.symm remainderAxis)).transpose
    let v := addressMod (prime^w) z ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm
    let D := diagonal parent
    let R := M8.ReversedExchange.rev (R := ZMod (prime^w)) 64
    let node := (fromBlocks D 0 0 R).mulVec v
    let changeBasis := fromBlocks (H * diagonal (Ring.inverse ∘ parent)) 0 0 (H * R)
    sweepAddress (w := w) b j lane z =
      stagedOwnerIndex b (FlatCoordinateLayout.index ((changeBasis.mulVec node) ∘ (@finSumFinEquiv 64 64).symm) j) := by
  intro c H v D R node changeBasis
  have weights := Weighted.diagonal_inv_mul (Ring.inverse ∘ parent) parent
    (fun i => Ring.inverse_mul_cancel _ (units i))
  have cancel : changeBasis * fromBlocks D 0 0 R = fromBlocks H 0 0 H := by
    simp [changeBasis,D,R,fromBlocks_multiply,mul_assoc,weights,M8.ReversedExchange.rev_mul_rev]
  change _ = stagedOwnerIndex b (FlatCoordinateLayout.index ((changeBasis *ᵥ ((fromBlocks D 0 0 R) *ᵥ v)) ∘ _) j)
  rw [mulVec_mulVec,cancel,fromBlocks_mulVec]
  have field (f : Axis → ZMod (prime^w)) (k : Fin 64) :
      (((reduce (prime^w) c.fullChart).transpose *ᵥ f) (remainderAxis k)) =
        (H *ᵥ (f ∘ stageAxis.symm)) k := by
    change _ = (((reduce (prime^w) c.fullChart).transpose.submatrix remainderAxis stageAxis.symm) *ᵥ _) k
    rw [submatrix_mulVec_equiv]
    simp [Function.comp_assoc]
  apply congrArg (fun digits => stagedOwnerIndex b (FlatCoordinateLayout.index digits j))
  funext k
  obtain ⟨k,rfl⟩ := (@finSumFinEquiv 64 64).surjective k
  cases k <;> simp [helperSlotField,helperFieldOrder,Function.comp_def,field,c,v]

/-- The inactive sweep realizes the rational stage action in the port's
entry chart, including addresses outside the denominator-coprime lattice. -/
theorem sweepEffect_inactive_read {n : Fin 9} {w B W : ℕ} {x y : OwnerArray w B W}
    (step : sweepEffect n w B W x y) (r : Role) (inactive : r.bank.val / 2 ≠ BitHosting.activePair n.val)
    (b : Fin B) (j : Fin W) :
    readLanes (sweepAddress (w := w) b j) y r =
      (Piece.stage n).run (readLanes (sweepAddress (w := w) b j) x) r := by
  let addr := fun (v : Axis ⊕ Axis → ZMod (prime^w)) =>
    let digits := helperSlotField (port r.port.val) none w (v ∘ Sum.inl,v ∘ Sum.inr)
    stagedOwnerIndex b (FlatCoordinateLayout.index digits j)
  let P := familySum n r
  let m := prime^w
  obtain ⟨adm,idem⟩ := familySum_projector n r w
  have comp := ModularFrameSchedule.admissible_sub m (admissible_one m) adm
  have legal : Admissible m (exchange P) := by
    intro i k
    cases i <;> cases k <;> first | apply comp | apply adm
  have reduced : reduce m (exchange P) = Matrix.fromBlocks (1-reduce m P) (reduce m P) (reduce m P) (1-reduce m P) := by
    have sub := ModularFrameSchedule.reduce_sub m (admissible_one m) adm
    rw [reduce_one] at sub
    ext i k
    cases i <;> cases k <;> first | rfl | exact congrFun (congrFun sub _) _
  rw [Piece.run,stagePiece_inactive _ _ _ inactive]
  let tape := bankTape r.bank (r.replica,r.port,r.cls)
  apply modularExchange_read m P idem legal (fun v => x tape (addr v)) (fun v => y tape (addr v))
  intro v
  rw [reduced,Matrix.fromBlocks_mulVec]
  simpa only [m,P,tape,bankTape,addr,stagedOwnerIndex_index,Function.comp_def,Sum.elim_inl,Sum.elim_inr,M8.Exchange.exchange] using
    sweepEffect_inactive step r inactive b j (v ∘ Sum.inl,v ∘ Sum.inr)

/-- On the active copy the source undergoes its frame change and the target
receives the framed XOR, after collapsing the label rows. -/
theorem sweepEffect_active {n : Fin 9} {w B W : ℕ} {x y : OwnerArray w B W}
    (step : sweepEffect n w B W x y) (run : Fin 32 × Fin 5) (t : Fin 111)
    (z : LabelEntry.Cell (copyLabelLayout w B ((prime^w)^112*W)) B) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n run.1 run.2,ownerTape_injective ..⟩
    let j : Fin (B*((prime^w)^112*W)) := finProdFinEquiv (z.b,z.after)
    let initial := fun i => (selectedFrame w (Frames.initialRefs i)).symm (phaseRead owner x j i)
    phaseRead owner y j (111+t.val) =
      selectedFrame w (Frames.finalRefs (111+t.val)) (initial (111+t.val) + initial t.val) ∧
    phaseRead owner y j t.val = selectedFrame w (Frames.finalRefs t.val) (initial t.val) := by
  classical
  intro owner j initial
  obtain ⟨packed,out,⟨trace,restore⟩,rfl⟩ := step
  let label := firstRowLabel w
  let data := collapseLabelBank (w := w) (B := B) (K := (prime^w)^112*W) out
  have read (i : ℕ) (hi : i < 661) :
      phaseRead owner (Function.update data (Fin.last 142080) (fun _ => 0)) j i = phaseRead owner data j i := by
    funext s
    simp only [phaseRead,Copy.extendStored,dite_eq_left hi,
      Function.update_of_ne (show owner ⟨i,hi⟩ ≠ Fin.last 142080 from Fin.castSucc_ne_last _)]
  rw [read _ (by omega),read _ (by omega)]
  constructor
  · simpa only [data,owner,j,initial,collapse_singleLabelBank] using
      (restoredStage_active n run w B W _ packed out trace restore t z).1
  · have sum := collapseLabelBank_read out owner z (⟨t.val,by omega⟩ : Fin 661)
    change phaseRead owner data j t.val = _ at sum
    rw [sum]
    calc
      _ = ∑ g : LabelPadding.Label 64 w, if g = label then selectedFrame w (Frames.finalRefs t.val)
          (initial t.val) else 0 := Finset.sum_congr rfl fun g _ =>
            restoredStage_sourceLabel n run w B W label x packed out trace restore t z g
      _ = _ := by simp

open AffineFieldCoordinates FlatCoordinateLayout Matrix in
/-- The physical entry correction on the compact source and exit correction
on the compact target convert a completed sweep to the translated port frame. -/
theorem sweepEffect_correctedPort [M8.Machine.Net] (t : Fin 111) :
    ∃ c preTapes postTapes preStates postStates : ℕ, ∀ w B W, 0 < w → 0 < B*((prime^w)^112*W) →
      let K := (prime^w)^112*W
      let V := (prime^w)^16*(B*K)
      let P := translatedPortProjector (ZMod (prime^w)) (4 : ZMod (prime^w))⁻¹ t
      ∃ enter leave : SharedBankStage.Stage _ 1 prime (@portOwner V),
        enter.tapes = preTapes ∧ leave.tapes = postTapes ∧
        enter.states = preStates ∧ leave.states = postStates ∧
        enter.cost+leave.cost = c*V + 2*LeafCore.coreCost V w+12 ∧
        ∀ n (run : Fin 32 × Fin 5) (x a y : OwnerArray w B W),
          let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n run.1 run.2,ownerTape_injective ..⟩
          let src := owner ⟨t.val,by omega⟩
          let dst := owner ⟨111+t.val,by omega⟩
          a src = enter.transform (x src) → a dst = x dst → sweepEffect n w B W a y →
          ∀ (z : LabelEntry.Cell (copyLabelLayout w B K) B) s,
            let cell := fun v => index (embed v) (@finProdFinEquiv B K (z.b,z.after))
            y src (cell s) = x src (cell (M8.Exchange.exchange P s.swap)) ∧
            leave.transform (y dst) (cell s) =
              x dst (cell (M8.Exchange.exchange (1-P) s)) + x src (cell s.swap) := by
  obtain ⟨a,preMachine,pre⟩ := portCorrection_owner t false true
  obtain ⟨b,postMachine,post⟩ := portCorrection_owner t true true
  refine ⟨a+b,preMachine.tapes,postMachine.tapes,preMachine.states,postMachine.states,?_⟩
  intro w B W hw hW K V P
  obtain ⟨enter,hpre,entryCost,entry⟩ := pre w (B*K) hw hW
  obtain ⟨leave,hpost,exitCost,exitRow⟩ := post w (B*K) hw hW
  refine ⟨enter,leave,congrArg SharedBankSkeleton.Skeleton.tapes hpre,congrArg SharedBankSkeleton.Skeleton.tapes hpost,
    congrArg SharedBankSkeleton.Skeleton.states hpre,congrArg SharedBankSkeleton.Skeleton.states hpost,?_,?_⟩
  · rw [entryCost,exitCost]
    simp only [ite_true,V]
    ring
  intro n run x a y owner src dst source target step z s cell
  let j : Fin (B*K) := @finProdFinEquiv B K (z.b,z.after)
  let U := reduce (prime^w) (selectedProjector ⟨2+t.val,by omega⟩)
  let T := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
  obtain ⟨up,pu,tc,ct,srcFrame,dstFrame⟩ := portFrame_absorption w t
  have readSrc (v) : phaseRead owner a j t.val v = a src (cell v) := by
    simp only [phaseRead,Copy.extendStored,dite_eq_left (show t.val < 661 by omega),src,cell,j]
  have readDst (v) : phaseRead owner a j (111+t.val) v = a dst (cell v) := by
    simp only [phaseRead,Copy.extendStored,dite_eq_left (show 111+t.val < 661 by omega),dst,cell,j]
  have decoded : (selectedFrame w (Frames.initialRefs t.val)).symm (phaseRead owner a j t.val) =
      fun v => x src (cell (M8.Exchange.exchange P v)) := by
    apply (selectedFrame w _).injective
    rw [LinearEquiv.apply_symm_apply]
    funext v
    rw [srcFrame,readSrc,source]
    exact entry (x src) v j
  obtain ⟨outT,outS⟩ := sweepEffect_active step run t z
  dsimp only at outT outS
  rw [(source_frames _ t.isLt).2.2] at outS
  rw [(target_frames _ t.isLt).1,emptyFrame_decode] at outT
  have tt : T*T=T := by calc
    T*T = T*((1-P)*T) := congrArg (T*·) ct.symm
    _ = T := by rw [← mul_assoc,tc,ct]
  have pp : P*P=P := by calc
    P*P = P*(U*P) := congrArg (P*·) up.symm
    _ = P := by rw [← mul_assoc,pu,up]
  have swap : M8.Exchange.exchange P (M8.Exchange.exchange (1-P) s) = s.swap := by
    rw [show M8.Exchange.exchange (1-P) s = M8.Exchange.exchange P s.swap by simp [M8.Exchange.exchange,add_comm],
      M8.Global.exchange_involutive pp]
  constructor
  · have h := congrFun outS s
    rw [fullFrame_read,decoded] at h
    simpa only [phaseRead,Copy.extendStored,dite_eq_left (show t.val < 661 by omega)] using h
  · let v := M8.Exchange.exchange (1-P) s
    have h := congrFun outT (M8.Exchange.exchange T v)
    rw [dstFrame,show M8.Exchange.exchange T (M8.Exchange.exchange T v) = v from M8.Global.exchange_involutive tt v,
      Pi.add_apply,decoded,readDst,target] at h
    apply (exitRow (y dst) s j).trans
    simpa only [phaseRead,Copy.extendStored,dite_eq_left (show 111+t.val < 661 by omega),v,swap,ite_true,T,dst,j,P] using h

end IntegerMultBounds.MathlibTM2.M6.BitNode
