module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepPortCorrection

/-! Read a corrected active sweep at rational window addresses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)
open Swap.Modular Matrix M8.RevMachine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

noncomputable def windowState (w : ℕ) (z : Axis ⊕ Axis → ℚ) :
    Swap.Shear.State Axis (ZMod (prime^w)) := (addressMod (prime^w) z ∘ Sum.inl,addressMod (prime^w) z ∘ Sum.inr)

private theorem windowState_exchange (w : ℕ) (n : Fin 9) {U : Matrix (Fin 8) (Fin 8) ℚ}
    (adm : Admissible (prime^w) U) (idem : U*U = U) (z : Axis ⊕ Axis → ℚ) :
    let L := diagonal fun i : Exterior => if i.1.val < n.val then (1 : ZMod (prime^w)) else 0
    windowState w ((exchange (windowProj n U)).mulVec z) =
      M8.Exchange.exchange (fromBlocks (reduce (prime^w) U) 0 0 L) (windowState w z) := by
  intro L
  let m := prime^w
  let A := windowProj n U
  have legal : Admissible m A := by
    rintro (i|i) (j|j)
    · exact adm i j
    · simp [A,windowProj]
    · simp [A,windowProj]
    · simp only [A,windowProj,fromBlocks_apply₂₂,lower,diagonal_apply]
      split_ifs <;> simp
  have red : reduce m A = fromBlocks (reduce m U) 0 0 L := by
    ext (i|i) (j|j)
    all_goals simp only [A,reduce,Matrix.map_apply,windowProj,fromBlocks_apply₁₁,fromBlocks_apply₁₂,
      fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.zero_apply,ratMod_zero,L,lower,diagonal_apply]
    split_ifs <;> simp [ratMod_zero,ratMod_one]
  have comp := ModularFrameSchedule.admissible_sub m (admissible_one m) legal
  have good : Admissible m (exchange A) := by
    intro i j
    cases i <;> cases j <;> first | apply comp | apply legal
  have sub := ModularFrameSchedule.reduce_sub m (admissible_one m) legal
  rw [reduce_one] at sub
  have blocks : reduce m (exchange A) = fromBlocks (1-reduce m A) (reduce m A) (reduce m A) (1-reduce m A) := by
    ext i j
    cases i <;> cases j <;> first | rfl | exact congrFun (congrFun sub _) _
  unfold windowState
  rw [addressMod_involution m good (exchange_mul_self (windowProj_mul_self n idem)),blocks,red,fromBlocks_mulVec]
  rfl

private theorem portLine_admissible (w : ℕ) (t : Fin 111) :
    Admissible (prime^w) (port t.val).lineProj := by
  have unit : IsUnit (4 : ZMod (prime^w)) := by simpa using prefix_denominator_unit 4 (by decide) (by decide) w
  have quarter : ((4:ℚ)⁻¹).den.Coprime (prime^w) := by simpa using (ZMod.isUnit_iff_coprime 4 _).mp unit
  intro i j
  change (((_:ℚ)*_)/4).den.Coprime _
  rw [div_eq_mul_inv,mul_comm,← Int.cast_mul]
  exact Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd ..) (Nat.Coprime.mul_left quarter
    (by rw [Rat.den_intCast]; exact Nat.coprime_one_left _))

/-- At rational addresses the two corrected streams agree with the certified
word in register order, including the reflected stages. -/
private theorem activeWord_read (n : Fin 9) (t : Fin 111) (w : ℕ)
    (src dst srcOut dstOut : Swap.Shear.State Axis (ZMod (prime^w)) → ZMod 2)
    (step : ∀ s, let L := diagonal fun i : Exterior => if i.1.val < n.val then (1 : ZMod (prime^w)) else 0
      let frame := fun (P : Matrix (Fin 8) (Fin 8) (ZMod (prime^w))) =>
        M8.Exchange.exchange (fromBlocks P 0 0 L)
      let P := reduce (prime^w) (port t.val).lineProj
      srcOut s = src (frame P (frame 1 s)) ∧
      dstOut s = dst (frame (1-P) (frame 0 s)) + src (frame 1 (frame 0 s)))
    (v : ℕ → Stream) (high : ∀ j, 661 ≤ j → v j = 0)
    (source : v t.val = src ∘ windowState w) (target : v (111+t.val) = dst ∘ windowState w) :
    srcOut ∘ windowState w = runWord n v t.val ∧ dstOut ∘ windowState w = runWord n v (111+t.val) := by
  let m := prime^w
  let P := (port t.val).lineProj
  have idem : P*P=P := PortCertificate.lineProj_mul_self (port_checked _ t.isLt)
  have adm := portLine_admissible w t
  have cp : (1-P)*(1-P)=1-P := by simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,idem,sub_self,sub_zero]
  have ca := ModularFrameSchedule.admissible_sub m (admissible_one m) adm
  have red := ModularFrameSchedule.reduce_sub m (admissible_one m) adm
  rw [reduce_one] at red
  let E := fun U => exchange (windowProj n U)
  have order : E 0 * E (1-P) = E (1-P) * E 0 := by simp [E,windowChange]
  have cross : E P * E (1-P) = E 1 * E 0 := by
    simp [E,windowChange,Matrix.mul_sub,idem]
  rw [runWord_forward n v high,forward_source n v high t.val t.isLt,forward_target n v high t.val t.isLt,
    source,target,order,cross]
  have zero := windowState_exchange w n (U := 0) (by intro i j; simp) (by simp)
  have one := windowState_exchange w n (U := 1) (admissible_one _) (by simp)
  have proj := windowState_exchange w n adm idem
  have comp := windowState_exchange w n ca cp
  have zred : reduce m (0 : Matrix (Fin 8) (Fin 8) ℚ) = 0 := by ext i j; exact ratMod_zero m
  dsimp only [P,m] at proj comp zred red
  constructor <;> funext z
  all_goals simp only [Pi.add_apply,along_apply,Function.comp_apply,E,P,← mulVec_mulVec,
    proj,comp,zero,one,zred,reduce_one,red]
  · exact (step _).1
  · exact (step _).2

/-- The logical stage enters through the certified route of each active port. -/
noncomputable def activeSweepAddress {w B W : ℕ} (n : Fin 9) (b : Fin B) (j : Fin W) (lane : BankLane)
    (z : Axis ⊕ Axis → ℚ) : Fin ((prime^w)^16*(B*((prime^w)^112*W))) :=
  let route := (port lane.2.1.val).stageRoute n
  activeWindowAddress b (windowState w ((bar route.transpose).mulVec z)) j

/-- The active port reads the modular stage route on both field halves,
including rational points outside the denominator-coprime lattice. -/
theorem activeSweepAddress_modular {w B W : ℕ} (n : Fin 9) (b : Fin B) (j : Fin W)
    (lane : BankLane) (z : Axis ⊕ Axis → ℚ) :
    let H := reduce (prime^w) ((port lane.2.1.val).stageRoute n)
    activeSweepAddress n b j lane z =
      activeWindowEquiv w B W (b,M8.Exchange.transform H H (windowState w z),j) := by
  let c := port lane.2.1.val
  let R := c.stageRoute n
  have checked := port_checked _ lane.2.1.isLt
  have adm := stageRoute_admissible c checked n w
  have legal : Admissible (prime^w) (bar R) := by
    rintro (i|i) (j|j) <;> first | exact adm i j | simp [bar]
  have red : reduce (prime^w) (bar R) =
      fromBlocks (reduce (prime^w) R) 0 0 (reduce (prime^w) R) := by
    ext (i|i) (j|j) <;> simp [bar,reduce,ratMod_zero]
  dsimp only
  rw [activeWindowEquiv_apply]
  dsimp only [activeSweepAddress]
  rw [PortCertificate.stageRoute_transpose]
  congr 1
  unfold windowState
  rw [addressMod_involution _ legal (bar_mul_self (c.stageRoute_mul_self checked n)),red,fromBlocks_mulVec]
  simp [M8.Exchange.transform,R,c]

/-- Both active roles read the certified stage at every rational address
after the two charged sweeps over the port corrections. -/
theorem correctedSweep_active_read [M8.Machine.Net] :
    ∃ (C : ℝ) (tapes : ℕ), ∀ (n : Fin 9) (w B W : ℕ), 0 < w → 0 < B*((prime^w)^112*W) →
      let V := (prime^w)^16*(B*((prime^w)^112*W))
      ∃ enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        enter.tapes ≤ tapes ∧ leave.tapes ≤ tapes ∧
        ((enter.cost+leave.cost : ℕ) : ℝ) ≤ C*(w : ℝ)^M8.Machine.BudgetBound.tau*V ∧
        (∀ x i, (∀ k, sourceOwner n k ≠ i) → enter.transform x i = x i) ∧
        (∀ y i, (∀ k, targetOwner n k ≠ i) → leave.transform y i = y i) ∧
        ∀ x y, sweepEffect n w B W (enter.transform x) y →
          ∀ (k : (Fin 32 × Fin 5) × Fin 111) (b : Fin B) (j : Fin W),
            let read := readLanes (activeSweepAddress (w := w) n b j)
            let agrees := fun i => read (leave.transform y) (owner n k.1.1 k.1.2 i) =
              (Piece.stage n).run (read x) (owner n k.1.1 k.1.2 i)
            agrees k.2.val ∧ agrees (111+k.2.val) := by
  obtain ⟨C,tapes,build⟩ := sweepPortCorrections
  refine ⟨C,tapes,?_⟩
  intro n w B W hw hW V
  obtain ⟨enter,leave,et,lt,paid,kept,off,ports⟩ := build n w B W hw hW
  refine ⟨enter,leave,et,lt,paid,kept,off,?_⟩
  intro x y step k b j read agrees
  let out := leave.transform y
  let t := k.2
  let R := (port t.val).stageRoute n
  let reg := registers n k.1.1 k.1.2 (read x)
  let raw := fun (a : OwnerArray w B W) i s => a i (activeWindowAddress b s j)
  have route : R.transpose = R := PortCertificate.stageRoute_transpose n
  have cancel : bar R * bar R = 1 := bar_mul_self (PortCertificate.stageRoute_mul_self (port_checked _ t.isLt) n)
  have get (a : OwnerArray w B W) (i : Fin 661) (portAt : (owner n k.1.1 k.1.2 i.val).port = t) :
      read a (owner n k.1.1 k.1.2 i.val) =
        along (bar R.transpose) (raw a (ownerTape n k.1.1 k.1.2 i) ∘ windowState w) := by
    funext z
    simp only [read,readLanes,readRoles,activeSweepAddress,portAt,R,along_apply,Function.comp_apply,raw]
    rw [← portAt]
    rfl
  have installed (i : Fin 661) (portAt : (owner n k.1.1 k.1.2 i.val).port = t) (chartAt : chart n i.val = R) :
      reg i.val = raw x (ownerTape n k.1.1 k.1.2 i) ∘ windowState w := by
    rw [show reg i.val = _ from registers_data n k.1.1 k.1.2 (read x) i.val i.isLt,chartAt,get x i portAt]
    funext z
    simp only [along_apply,route,mulVec_mulVec,cancel,one_mulVec]
  let src : Fin 661 := ⟨t.val,by omega⟩
  let dst : Fin 661 := ⟨111+t.val,by omega⟩
  have srcPort : (owner n k.1.1 k.1.2 src.val).port = t := by
    change (owner n k.1.1 k.1.2 t.val).port = t
    rw [owner_source]; rfl
  have dstPort : (owner n k.1.1 k.1.2 dst.val).port = t := by
    change (owner n k.1.1 k.1.2 (111+t.val)).port = t
    rw [owner_target]; rfl
  obtain ⟨cs,cd⟩ := chart_port n t
  obtain ⟨source,target⟩ := activeWord_read n t w (raw x (sourceOwner n k)) (raw x (targetOwner n k))
    (raw out (sourceOwner n k)) (raw out (targetOwner n k)) (fun s => ports x y step k b s j)
    reg (registers_high n k.1.1 k.1.2 (read x)) (installed src srcPort cs) (installed dst dstPort cd)
  have finish (i : Fin 661) (portAt : (owner n k.1.1 k.1.2 i.val).port = t) (chartAt : chart n i.val = R)
      (side : ℕ) (hs : side < 2) (role : owner n k.1.1 k.1.2 i.val = sideRole n k.1.1 k.1.2 side t)
      (word : raw out (ownerTape n k.1.1 k.1.2 i) ∘ windowState w = runWord n reg i.val) : agrees i.val := by
    change read out _ = stagePiece n (read x) _
    rw [get out i portAt,role,stagePiece_side n (read x) _ _ _ side hs,← role,invoke_owner _ _ _ _ _ i.isLt,
      chartAt,word]
  exact ⟨finish src srcPort cs _ (by omega) (owner_source ..) source,
    finish dst dstPort cd _ (by omega) (owner_target ..) target⟩

/-- Interpret the active window and the inactive port charts on the same
bank of compact physical owners. -/
noncomputable def sweepRoles {w B W : ℕ} (n : Fin 9) (b : Fin B) (j : Fin W)
    (a : OwnerArray w B W) : State := fun r =>
  if r.bank.val / 2 = BitHosting.activePair n.val then readLanes (activeSweepAddress n b j) a r
  else readLanes (sweepAddress b j) a r

/-- Each role in a stage addresses its compact owner by a permutation of
the same modular parent states, inherited blocks and spectator positions. -/
noncomputable def sweepRoleEquiv (w B W : ℕ) (n : Fin 9) (r : Role) :
    Fin B × (Swap.Shear.State Axis (ZMod (prime^w)) × Fin W) ≃
      Fin ((prime^w)^16*(B*((prime^w)^112*W))) :=
  let lane : BankLane := (r.replica,r.port,r.cls)
  if r.bank.val / 2 = BitHosting.activePair n.val then
    let c := port r.port.val
    let H := reduce (prime^w) (c.stageRoute n)
    let checked := port_checked _ r.port.isLt
    let adm := stageRoute_admissible c checked n w
    let invol := reduce_inverse _ adm adm (c.stageRoute_mul_self checked n)
    let route := M8.Exchange.transform H H
    let undo : Function.Involutive route := fun s => by
      simp [route,M8.Exchange.transform,mulVec_mulVec,show H*H=1 from invol]
    ((Equiv.refl _).prodCongr ((undo.toPerm route).prodCongr (Equiv.refl _))).trans (activeWindowEquiv w B W)
  else inactiveWindowEquiv w B W lane

theorem sweepRoles_eq_read {w B W : ℕ} (n : Fin 9) (b : Fin B) (j : Fin W)
    (a : OwnerArray w B W) (r : Role) :
    sweepRoles n b j a r =
      readRoles (fun z => sweepRoleEquiv w B W n r (b,windowState w z,j)) a r := by
  by_cases active : r.bank.val / 2 = BitHosting.activePair n.val
  · simp only [sweepRoles,sweepRoleEquiv,active,↓reduceIte,readLanes]
    funext z
    exact congrArg (a (bankTape r.bank (r.replica,r.port,r.cls)))
      (activeSweepAddress_modular n b j (r.replica,r.port,r.cls) z)
  · simp only [sweepRoles,active,↓reduceIte,readLanes,sweepRoleEquiv,windowState,inactiveWindowEquiv_read]

/-- One corrected physical sweep realizes the logical stage simultaneously
on every role at every inherited block and spectator. -/
theorem correctedSweep_read [M8.Machine.Net] :
    ∃ (C : ℝ) (tapes : ℕ), ∀ (n : Fin 9) (w B W : ℕ), 0 < w → 0 < B*((prime^w)^112*W) →
      let V := (prime^w)^16*(B*((prime^w)^112*W))
      ∃ enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        enter.tapes ≤ tapes ∧ leave.tapes ≤ tapes ∧
        ((enter.cost+leave.cost : ℕ) : ℝ) ≤ C*(w : ℝ)^M8.Machine.BudgetBound.tau*V ∧
        ∀ x y, sweepEffect n w B W (enter.transform x) y → ∀ b j,
          sweepRoles n b j (leave.transform y) = (Piece.stage n).run (sweepRoles n b j x) := by
  obtain ⟨C,tapes,build⟩ := correctedSweep_active_read
  refine ⟨C,tapes,?_⟩
  intro n w B W hw hW V
  obtain ⟨enter,leave,et,lt,paid,kept,off,acts⟩ := build n w B W hw hW
  refine ⟨enter,leave,et,lt,paid,?_⟩
  intro x y step b j
  let active := readLanes (activeSweepAddress (w := w) n b j)
  let inactive := readLanes (sweepAddress (w := w) b j)
  funext r
  by_cases hr : r.bank.val / 2 = BitHosting.activePair n.val
  · have side := role_side n r hr
    let k := ((r.replica,r.cls),r.port)
    obtain ⟨src,dst⟩ := acts x y step k b j
    have eqn : active (leave.transform y) r = stagePiece n (active x) r := by
      by_cases h : r.bank.val % 2 = n.val % 2
      · rw [h] at side
        simpa only [k,owner_source,← side,active,Piece.run] using src
      · rw [show r.bank.val % 2 = 1-n.val % 2 by omega] at side
        simpa only [k,owner_target,← side,active,Piece.run] using dst
    rw [show sweepRoles n b j (leave.transform y) r = active (leave.transform y) r from ite_eq_left hr,eqn]
    change stagePiece n (active x) r = stagePiece n (sweepRoles n b j x) r
    have val (side : ℕ) (h : side < 2) : sweepRoles n b j x (sideRole n r.replica r.cls side r.port) =
        active x (sideRole n r.replica r.cls side r.port) := ite_eq_left (side_pair _ _ _ _ h _)
    rcases Nat.mod_two_eq_zero_or_one r.bank.val with e|e <;> rw [e] at side
    · conv => lhs; rw [side,stagePiece_side_zero]
      conv => rhs; rw [side,stagePiece_side_zero]
      rw [val 0 (by decide),val 1 (by decide)]
    · conv => lhs; rw [side,stagePiece_side_one]
      conv => rhs; rw [side,stagePiece_side_one]
      rw [val 0 (by decide),val 1 (by decide)]
  · let tape := bankTape r.bank (r.replica,r.port,r.cls)
    have outside (k : (Fin 32 × Fin 5) × Fin 111) (i : Fin 661) (hi : i.val < 222) :
        ownerTape n k.1.1 k.1.2 i ≠ tape := by
      intro eq
      have same : owner n k.1.1 k.1.2 i.val = r := (Fintype.equivFin Role).injective
        (Fin.cast_injective _ (Fin.castSucc_injective _ eq))
      apply hr
      rw [← same]
      simp only [owner,hi,ite_true]
      apply side_pair
      unfold regSide
      split <;> omega
    have entry := kept x tape (fun k => outside k _ (by change k.2.val < 222; omega))
    have exitRow := off y tape (fun k => outside k _ (by change 111+k.2.val < 222; omega))
    rw [show sweepRoles n b j (leave.transform y) r = _ from ite_eq_right hr]
    change inactive (leave.transform y) r = stagePiece n (sweepRoles n b j x) r
    rw [stagePiece_inactive _ _ _ hr,show sweepRoles n b j x r = _ from ite_eq_right hr]
    have action := sweepEffect_inactive_read step r hr b j
    rw [Piece.run,stagePiece_inactive _ _ _ hr] at action
    have input : inactive (enter.transform x) r = inactive x r := funext fun z => congrFun entry _
    have output : inactive (leave.transform y) r = inactive y r := funext fun z => congrFun exitRow _
    exact output.trans (action.trans (congrArg (along (exchange (familySum n r))) input))

end IntegerMultBounds.MathlibTM2.M6.BitNode
