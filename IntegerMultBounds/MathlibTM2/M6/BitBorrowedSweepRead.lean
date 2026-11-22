module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedHelper
public import IntegerMultBounds.MathlibTM2.M6.BitSweepPortCorrection

/-! Logical role reads on independently occupied labels of a packed sweep. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine Swap.Modular
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

noncomputable def borrowedRoleCell {w B K : ℕ} (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (r : Role) (v : Axis ⊕ Axis → ZMod (prime^w)) : ℕ :=
  let row := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
    rw [← pow_mul]; congr 1; omega)
  let suffix := finProdFinEquiv (finProdFinEquiv (b,row),t)
  let s := (v ∘ Sum.inl,v ∘ Sum.inr)
  helperFieldCell (helperSlotField (port r.port.val) none w s) (0 : Fin 1) suffix

noncomputable def borrowedRoleRead {V w B K : ℕ} (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (data : Fin 142081 → Fin V → ZMod 2) : State := fun r =>
  (fun v => M8.RevMachine.ext (data (bankTape r.bank (r.replica,r.port,r.cls))) (borrowedRoleCell b t g r v)) ∘ addressMod (prime^w)

private theorem family_read {n : Fin 9} {w : ℕ} (r : Role)
    (before after : (Axis ⊕ Axis → ZMod (prime^w)) → ZMod 2)
    (physical : ∀ v, let s := M8.Exchange.exchange (reduce (prime^w) (familySum n r)) (v ∘ Sum.inl,v ∘ Sum.inr)
                     after (Sum.elim s.1 s.2) = before v) :
    after ∘ addressMod (prime^w) = along (exchange (familySum n r)) (before ∘ addressMod (prime^w)) := by
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
  apply modularExchange_read m P idem legal before after
  intro v
  rw [reduced,Matrix.fromBlocks_mulVec]
  exact physical v

/-- Each inactive role realizes its logical family exchange at every label
of the same execution, including labels with independently chosen inputs. -/
theorem borrowedSweep_modular {n w B K x y out}
    (trace : stageRuns.foldr (fun p next a => ∃ b, borrowedPackedStep n w B K p a b ∧ next b) (· = y) x)
    (restore : HelperLabelTrace w 1 (B*prime^(64*(w*64))*K) (restoreSlotChanges (stageFinalSlot n)) y out)
    (r : Role) (inactive : r.bank.val / 2 ≠ BitHosting.activePair n.val)
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w) :
    let tape := bankTape r.bank (r.replica,r.port,r.cls)
    let read := fun a v => M8.RevMachine.ext (a : Fin ((prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)) → ZMod 2) (borrowedRoleCell b t g r v)
    ∀ v, let s := M8.Exchange.exchange (reduce (prime^w) (familySum n r)) (v ∘ Sum.inl,v ∘ Sum.inr)
         read (out tape) (Sum.elim s.1 s.2) = read (x tape) v := by
  intro tape read v
  exact borrowedRestored_inactive trace restore r inactive b t g (v ∘ Sum.inl,v ∘ Sum.inr)

private theorem stage_inactive_of_read (n : Fin 9) (r : Role) (a b : State)
    (inactive : r.bank.val / 2 ≠ BitHosting.activePair n.val)
    (read : b r = along (exchange (familySum n r)) (a r)) :
    b r = (Piece.stage n).run a r :=
  read.trans (stagePiece_inactive n a r inactive).symm

theorem borrowedSweep_inactive_read {n w B K x y out}
    (trace : stageRuns.foldr (fun p next a => ∃ b, borrowedPackedStep n w B K p a b ∧ next b) (· = y) x)
    (restore : HelperLabelTrace w 1 (B*prime^(64*(w*64))*K) (restoreSlotChanges (stageFinalSlot n)) y out)
    (r : Role) (inactive : r.bank.val / 2 ≠ BitHosting.activePair n.val)
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w) :
    borrowedRoleRead b t g out r = (Piece.stage n).run (borrowedRoleRead b t g x) r := by
  apply stage_inactive_of_read n r (borrowedRoleRead b t g x) (borrowedRoleRead b t g out) inactive
  let tape := bankTape r.bank (r.replica,r.port,r.cls)
  let read := fun (a : Fin ((prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)) → ZMod 2) v => M8.RevMachine.ext a (borrowedRoleCell b t g r v)
  apply family_read r (read (x tape)) (read (out tape))
  exact borrowedSweep_modular trace restore r inactive b t g

open AffineFieldCoordinates FlatCoordinateLayout Matrix M8.RevMachine in
/-- Correct the active source and target on all borrowed labels with the
same two machines. Each correction scans the entire owner once at its stated price. -/
theorem borrowedSweep_correctedPort [M8.Machine.Net] (t : Fin 111) :
    ∃ c preTapes postTapes preStates postStates : ℕ, ∀ w B K, 0 < w → 0 < B*prime^(64*(w*64))*K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let P := translatedPortProjector (ZMod (prime^w)) (4 : ZMod (prime^w))⁻¹ t
      ∃ enter leave : SharedBankStage.Stage _ 1 prime (@portOwner V),
        enter.tapes = preTapes ∧ leave.tapes = postTapes ∧ enter.states = preStates ∧ leave.states = postStates ∧
        enter.cost+leave.cost = c*V + 2*LeafCore.coreCost V w+12 ∧
        ∀ n (run : Fin 32 × Fin 5) (x a y : Fin 142081 → Fin V → ZMod 2),
          let src := ownerTape n run.1 run.2 ⟨t.val,by omega⟩
          let dst := ownerTape n run.1 run.2 ⟨111+t.val,by omega⟩
          a src = enter.transform (x src) → a dst = x dst → BorrowedPorts n w B K a y →
          ∀ (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B) s,
            let cell := fun v => index (embed v) (labelSpectator g z)
            y src (cell s) = x src (cell (M8.Exchange.exchange P s.swap)) ∧
            leave.transform (y dst) (cell s) =
              x dst (cell (M8.Exchange.exchange (1-P) s)) + x src (cell s.swap) := by
  obtain ⟨c,et,lt,es,ls,build⟩ := framed_correctedPort t
  refine ⟨c,et,lt,es,ls,?_⟩
  intro w B K hw positive W V P
  obtain ⟨enter,leave,he,hl,qe,ql,cost,correct⟩ := build w W hw positive
  refine ⟨enter,leave,he,hl,qe,ql,cost,?_⟩
  intro n run x a y src dst source target ports g z
  obtain ⟨outS,outT⟩ := ports run t g z
  exact correct n run x a y source target (labelSpectator g z) outT outS

open AffineFieldCoordinates FlatCoordinateLayout in
/-- A shared entry pass and exit pass correct all 17760 port pairs on the
borrowed bank. The price is charged on the full volume once per pass. -/
theorem borrowedPortCorrections [M8.Machine.Net] :
    ∃ (C : ℝ) (base tapes states : ℕ), ∀ (n : Fin 9) (w B K : ℕ), 0 < w → 0 < B*prime^(64*(w*64))*K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      ∃ enter leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        enter.tapes ≤ tapes ∧ leave.tapes ≤ tapes ∧ enter.states ≤ states ∧ leave.states ≤ states ∧
        enter.cost + leave.cost = base*V + 17760*(2*M8.RevMachine.LeafCore.coreCost V w+14) ∧
        ((enter.cost+leave.cost : ℕ) : ℝ) ≤ C*(w : ℝ)^M8.Machine.BudgetBound.tau*V ∧
        (∀ x i, (∀ k, sourceOwner n k ≠ i) → enter.transform x i = x i) ∧
        (∀ y i, (∀ k, targetOwner n k ≠ i) → leave.transform y i = y i) ∧
        ∀ x y, BorrowedPorts n w B K (enter.transform x) y →
          ∀ (k : (Fin 32 × Fin 5) × Fin 111) (g : LabelPadding.Label 64 w)
            (z : LabelEntry.Cell (copyLabelLayout w B K) B) s,
          let j := labelSpectator g z
          let P := translatedPortProjector (ZMod (prime^w)) (4 : ZMod (prime^w))⁻¹ k.2
          let cell := fun v => index (embed v) j
          let src := sourceOwner n k
          let dst := targetOwner n k
          leave.transform y src (cell s) = x src (cell (M8.Exchange.exchange P s.swap)) ∧
          leave.transform y dst (cell s) = x dst (cell (M8.Exchange.exchange (1-P) s)) + x src (cell s.swap) := by
  obtain ⟨C,base,tapes,states,build⟩ := framedPortCorrections
  refine ⟨C,base,tapes,states,?_⟩
  intro n w B K hw positive W V
  obtain ⟨enter,leave,et,lt,es,ls,exactCost,cost,keep,off,correct⟩ := build n w W hw positive
  refine ⟨enter,leave,et,lt,es,ls,exactCost,cost,keep,off,?_⟩
  intro x y ports k g z s
  obtain ⟨source,target⟩ := ports k.1 k.2 g z
  exact correct x y k (labelSpectator g z) target source s

end IntegerMultBounds.MathlibTM2.M6.BitNode
