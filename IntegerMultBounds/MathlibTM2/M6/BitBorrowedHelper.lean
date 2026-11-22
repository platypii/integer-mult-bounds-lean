module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedNode
public import IntegerMultBounds.MathlibTM2.M6.BitPackedStage

/-! Interpret the scheduled helper slots at the aligned borrowed-row addresses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- In the aligned layout all owner and label coordinates follow the 128
digits. The existing slot packer therefore uses a unit gap and carries the
whole borrowed row in its trailing record. -/
theorem alignedOffset_label {w B K} (live : Fin 16 → ZMod (prime^w))
    (exterior : Fin 112 → ZMod (prime^w))
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w) :
    let row := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
      rw [← pow_mul]; congr 1; omega)
    (alignedOffset live exterior b t g).val =
      helperLabelCell live (0 : Fin 1) exterior (finProdFinEquiv (finProdFinEquiv (b,row),t)) := by
  intro row
  simp only [alignedOffset,FlatCoordinateLayout.index_val,labelSpectator,alignedCell,
    helperLabelCell,finProdFinEquiv_apply_val,row,Fin.val_cast,Fin.val_zero,mul_one,add_zero]
  ring

open M8.RevMachine in
/-- Packing a helper before its borrowed invocation realizes the exchange on
its assigned eight-dimensional span for every independent row. -/
theorem borrowedPacked_helper {n p w B K before x packed y}
    (pack : HelperLabelTrace w 1 (B*prime^(64*(w*64))*K) (scheduledSlotChanges n p before) x packed)
    (step : BorrowedStep n w ((prime^w)^112*B) K p packed y) (h : Fin 439)
    (c : PortCertificate) (checked : c.Checked) (s : Swap.Shear.State Axis (ZMod (prime^w)))
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w) :
    let row := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
      rw [← pow_mul]; congr 1; omega)
    let j := finProdFinEquiv (finProdFinEquiv (b,row),t)
    let change := helperSlotChange n p before h
    let slot := helperPosition (n,h)
    ext (y change.1) (helperFieldCell (helperSlotField c (some slot) w
      (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (c.span slot (slot+8 : ℕ))) s)) (0 : Fin 1) j) =
      ext (x change.1) (helperFieldCell (helperSlotField c change.2.1 w s) (0 : Fin 1) j) := by
  intro row j change slot
  let digits := helperSlotField c (some slot) w s
  let live := digits ∘ Fin.castAdd 112
  let exterior : Fin 112 → ZMod (prime^w) := digits ∘ Fin.natAdd 16
  let state : Swap.Shear.State (Fin 8) (ZMod (prime^w)) := (live ∘ Fin.castAdd 8,live ∘ Fin.natAdd 8)
  have embed : AffineFieldCoordinates.embed state = live := by
    funext i
    exact Fin.addCases (fun a => Fin.addCases_left ..) (fun a => Fin.addCases_right ..) i
  rw [helperFieldCell_exchange c checked slot w s]
  apply Eq.trans _ (scheduledLabelRead n p before x packed pack h c s (0 : Fin 1) j)
  change ext (y change.1) (helperLabelCell (AffineFieldCoordinates.embed state.swap) (0 : Fin 1) exterior j) =
    ext (packed change.1) (helperLabelCell live (0 : Fin 1) exterior j)
  rw [← alignedOffset_label _ exterior b t g,← alignedOffset_label live exterior b t g,
    ext_apply,ext_apply,← embed]
  exact step.helperRead g (alignedCell exterior b t) h state


def borrowedPackedStep (n : Fin 9) (w B K : ℕ) (p : Fin 32 × Fin 5)
    (x y : Fin 142081 → Fin ((prime^w)^16*(((prime^w)^112*B)*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  let before := (stageRuns.take (stageRuns.idxOf p)).foldl (fun a k => helperChartsAfter n k a) (fun _ => none)
  ∃ packed, HelperLabelTrace w 1 (B*prime^(64*(w*64))*K) (scheduledSlotChanges n p before) x packed ∧
    BorrowedStep n w ((prime^w)^112*B) K p packed y

/-- Packing only helper owners preserves the borrowed port equations of
the invocation, including the source term added into the target. -/
theorem borrowedPacked_ports {n w B K x y}
    (trace : stageRuns.foldr (fun p next a => ∃ b, borrowedPackedStep n w B K p a b ∧ next b) (· = y) x) :
    BorrowedPorts n w ((prime^w)^112*B) K x y := by
  intro run t g z owner j src dst read input
  let view := fun a => (read a src,read a dst)
  let action := fun (a b : AddressStream (ZMod (prime^w)) × AddressStream (ZMod (prime^w))) =>
    let source := (selectedFrame w (Frames.initialRefs src.val)).symm a.1
    b.1 = selectedFrame w (Frames.finalRefs src.val) source ∧
    b.2 = selectedFrame w (Frames.finalRefs dst.val) ((selectedFrame w (Frames.initialRefs dst.val)).symm a.2 + source)
  have packRead {p a packed} {before : Fin 142081 → Option (Fin 9 × Fin 439)}
      (pack : HelperLabelTrace w 1 (B*prime^(64*(w*64))*K) (scheduledSlotChanges n p before) a packed)
      (i : Fin 661) (data : i.val < 222) : read packed i = read a i := by
    have fixed := labelTrace_off _ _ _ pack (owner i) (by
      rintro q mem eqn
      obtain ⟨h,_,rfl⟩ := List.mem_map.mp mem
      by_cases same : p = run
      · subst p
        have hval := congrArg Fin.val (ownerTape_injective n run.1 run.2 eqn)
        change 222+h.val = i.val at hval
        omega
      · exact otherRunMissesPort n p run same _ i data eqn)
    funext state
    simpa only [read,phaseRead,Copy.extendStored,dite_eq_left i.isLt] using congrFun fixed
      (FlatCoordinateLayout.index (AffineFieldCoordinates.embed state) j)
  apply (uniqueTraceRead run view action (borrowedPackedStep n w B K) ?_ ?_ stageRuns stageRuns_nodup x y trace).1 (mem_stageRuns run)
  · rintro a b ⟨packed,pack,step⟩
    have hsrc := packRead pack src (by dsimp [src]; omega)
    have hdst := packRead pack dst (by dsimp [dst]; omega)
    change action (view a) (view b)
    have cell : action (view packed) (view b) := by
      simpa only [src,dst,action,view,read,Fin.val_mk,Nat.add_sub_cancel_left,
        show ¬(111 ≤ t.val ∧ t.val < 222) by omega,
        show 111 ≤ 111+t.val ∧ 111+t.val < 222 by omega,and_self,↓reduceDIte] using
        And.intro (step.dirtyRead g z src) (step.dirtyRead g z dst)
    simpa only [view,hsrc,hdst] using cell
  · rintro p other a b ⟨packed,pack,step⟩
    have kept (i : Fin 661) (hi : i.val < 222) : read b i = read a i := by
      apply Eq.trans _ (packRead pack i hi)
      have fixed := step.2 (owner i) (Fin.castSucc_ne_last _) (fun h => otherRunMissesPort n p run other h i hi)
      funext state
      simpa only [read,phaseRead,Copy.extendStored,dite_eq_left i.isLt] using congrFun fixed
        (FlatCoordinateLayout.index (AffineFieldCoordinates.embed state) j)
    exact Prod.ext (kept src (by dsimp [src]; omega)) (kept dst (by dsimp [dst]; omega))

open M8.RevMachine in
/-- Once the sweep restores its helper slots, each inactive role has
exchanged its complete family span in caller coordinates at every label. -/
theorem borrowedRestored_inactive {n w B K x y out}
    (trace : stageRuns.foldr (fun p next a => ∃ b, borrowedPackedStep n w B K p a b ∧ next b) (· = y) x)
    (restore : HelperLabelTrace w 1 (B*prime^(64*(w*64))*K) (restoreSlotChanges (stageFinalSlot n)) y out)
    (ρ : Role) (inactive : ρ.bank.val / 2 ≠ BitHosting.activePair n.val)
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w) :
    let row := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
      rw [← pow_mul]; congr 1; omega)
    let j := finProdFinEquiv (finProdFinEquiv (b,row),t)
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
    let read := fun word s => ext word (helperFieldCell (helperSlotField (port ρ.port.val) none w s) (0 : Fin 1) j)
    ∀ s, read (out tape) (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (familySum n ρ)) s) =
      read (x tape) s := by
  intro row j tape read s
  apply (restoreSlot_read (stageFinalSlot n) restore tape (port ρ.port.val) _ (0 : Fin 1) j).trans
  apply helperSweep_read n ρ inactive _ x y trace (0 : Fin 1) j _ _ s
  · rintro p a z ⟨packed,pack,step⟩ h state
    exact borrowedPacked_helper pack step h _ (port_checked _ ρ.port.isLt) state b t g
  · rintro p a z ⟨packed,pack,step⟩ miss
    exact (step.2 tape (Fin.castSucc_ne_last _) miss).trans (labelTrace_off _ _ _ pack tape (by
      rintro q mem
      obtain ⟨h,_,rfl⟩ := List.mem_map.mp mem
      exact miss _))


end IntegerMultBounds.MathlibTM2.M6.BitNode
