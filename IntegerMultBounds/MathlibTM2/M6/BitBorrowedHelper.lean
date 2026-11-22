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


open Stack Host Cover.Fallback M8.RevMachine in
/-- Pack the scheduled helpers and enter the borrowed invocation. The
resulting machine trace supplies the step consumed by the sweep proof. -/
theorem borrowedPackedCall_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (n : Fin 9) (p : Fin 32 × Fin 5) (fan : Fin (142081+2) ↪ Fin T)
    (capacity : columnCapacity ≤ Q) (body : P → Pr P T Q prime U)
    (headers : ℕ → Fin 6 → Fin T) (apart : ∀ i j (o : Fin 142081), headers i j ≠ fan (o.castAdd 2)) :
    let bank := Fin.castAddEmb LeafCore.small (n := T)
    let full := fan.trans bank
    let outer := fun f => embProg bank id (body f)
    ∃ pack, ∃ C : ℝ, ∀ w B K : ℕ,
      let W := B*prime^(64*(w*64))*K
      let blocks := (prime^w)^112*B
      let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
      0 < V → ∀ (data : Fin 142081 → Fin V → ZMod 2) u S call (price : ℝ),
      (∀ i : Fin 127, ∀ j, S.R (bank (headers i.val j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      HelperFan full data S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      (∀ a y D, HelperFan fan a D →
        (∀ j, (∀ h, fan h ≠ j) → D.L j = S.L (bank j) ∧ D.R j = S.R (bank j)) →
        ∃ z F m b, Exec body call (mk y D) m (mk z F) ∧ (m : ℝ) ≤ price ∧ z.user = y.user ∧
          HelperFan fan b F ∧ BorrowedStep n w blocks K p a b) →
      ∃ z F t b, Exec outer (.seq pack (embProg bank id call)) (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ C*((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+price ∧
        z.user = u.user ∧ HelperFan full b F ∧ borrowedPackedStep n w B K p data b := by
  intro bank full outer
  obtain ⟨pack,C,run⟩ := scheduledLabelTrace_exec n p (stageRuns.take (stageRuns.idxOf p))
    fan capacity body headers apart
  refine ⟨pack,C,?_⟩
  intro w B K W blocks V pos data u S call price stored rep free invoke
  let v : RecursiveInterchangeLayout.Descriptor := ⟨V,1,1,0,1,1⟩
  have size : RecursiveInterchangeLayout.volume prime v = V := by simp [RecursiveInterchangeLayout.volume,v]
  have atVolume := @run w 1 W v
  rw [size] at atVolume
  have dims : V = (prime^w)^16*(1*((prime^w)^112*W)) := by dsimp [V,blocks,W]; ring
  obtain ⟨z,F,t,a,b,exec,paid,same,done,act,trace⟩ := atVolume dims pos data u S call price
    (BorrowedStep n w blocks K p) stored rep free invoke
  exact ⟨z,F,t,b,exec,paid,same,done,a,trace,act⟩

open Stack Host Cover.Fallback M8.RevMachine in
/-- Execute the stage's final slot restoration on the aligned bank. The
same owner tapes hold the output, and the leaf workspace is ready to reuse. -/
theorem borrowedRestore_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (n : Fin 9) (fan : Fin (142081+2) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (body : P → Pr P (T+LeafCore.small) Q prime U) (headers : ℕ → Fin 6 → Fin T)
    (apart : ∀ i j (o : Fin 142081), headers i j ≠ fan (o.castAdd 2)) :
    let bank := Fin.castAddEmb LeafCore.small (n := T)
    let full := fan.trans bank
    ∃ code, ∃ C : ℝ, ∀ w B K : ℕ,
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)
      0 < V → ∀ (data : Fin 142081 → Fin V → ZMod 2) u S,
      (∀ i : Fin 127, ∀ j, S.R (bank (headers i.val j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      HelperFan full data S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ C*((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        z.user = u.user ∧ HelperFan full out F ∧
        HelperLabelTrace w 1 W (restoreSlotChanges (stageFinalSlot n)) data out ∧
        (∀ j : Fin T, (∀ o : Fin 142081, j ≠ fan (o.castAdd 2)) →
          F.L (bank j) = S.L (bank j) ∧ F.R (bank j) = S.R (bank j)) ∧
        ∀ j : Fin LeafCore.small, F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = [] := by
  intro bank full
  obtain ⟨code,C,run⟩ := helperFanChanges_exec fan (restoreSlotChanges (stageFinalSlot n)) capacity body headers apart
  refine ⟨code,C,?_⟩
  intro w B K W V pos data u S stored rep free
  let v : RecursiveInterchangeLayout.Descriptor := ⟨V,1,1,0,1,1⟩
  have size : RecursiveInterchangeLayout.volume prime v = V := by simp [RecursiveInterchangeLayout.volume,v]
  have atVolume := @run w 1 W v
  rw [size] at atVolume
  have dims : V = (prime^w)^16*(1*((prime^w)^112*W)) := by dsimp [V,W]; ring
  obtain ⟨z,F,t,out,same,exec,paid,done,trace,keep,clear⟩ := atVolume dims pos data u S stored rep free
  exact ⟨z,F,t,out,exec,paid,same,done,trace,keep,clear⟩

open Stack Host Cover.Fallback M8.RevMachine in
/-- Run the borrowed stage in occurrence order, with restoration as the final
program. Each private initialization is needed only until its own call. -/
theorem borrowedSweep_exec {T Q w B K : ℕ} {P U : Type} (n : Fin 9)
    (body : P → Pr P T Q prime U) (fan : Fin (142081+2) ↪ Fin T) :
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)
    ∀ (saved : Fin 32 × Fin 5 → Stacks T prime → Prop) (ready : Stacks T prime → Prop)
      (price : Fin 32 × Fin 5 → ℝ) (restorePrice : ℝ),
    (∀ p, ∃ code, ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan x S → ready S → saved p S →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ price p ∧ z.user = u.user ∧
        HelperFan fan y F ∧ borrowedPackedStep n w B K p x y ∧ ready F ∧
        ∀ j, j ≠ p → saved j S → saved j F) →
    (∃ code, ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan x S → ready S →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ restorePrice ∧ z.user = u.user ∧
        HelperFan fan y F ∧ HelperLabelTrace w 1 W (restoreSlotChanges (stageFinalSlot n)) x y) →
    ∃ code, ∀ x u S, HelperFan fan x S → ready S → (∀ j, saved j S) →
      ∃ z F t y out, Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ (stageRuns.map price).sum+restorePrice ∧
        z.user = u.user ∧ HelperFan fan out F ∧
        stageRuns.foldr (fun p next a => ∃ b, borrowedPackedStep n w B K p a b ∧ next b) (· = y) x ∧
        HelperLabelTrace w 1 W (restoreSlotChanges (stageFinalSlot n)) y out := by
  intro W V saved ready price restorePrice calls restore
  obtain ⟨last,finish⟩ := restore
  suffices fold : ∀ ls : List (Fin 32 × Fin 5), ls.Nodup → ∃ code, ∀ x u S, HelperFan fan x S →
      ready S → (∀ j ∈ ls, saved j S) → ∃ z F t y out, Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ (ls.map price).sum+restorePrice ∧ z.user = u.user ∧ HelperFan fan out F ∧
        ls.foldr (fun p next a => ∃ b, borrowedPackedStep n w B K p a b ∧ next b) (· = y) x ∧
        HelperLabelTrace w 1 W (restoreSlotChanges (stageFinalSlot n)) y out by
    obtain ⟨code,run⟩ := fold stageRuns stageRuns_nodup
    exact ⟨code,fun x u S live ok fresh => run x u S live ok (fun j _ => fresh j)⟩
  intro ls
  induction ls with
  | nil =>
    intro _
    refine ⟨last,?_⟩
    intro x u S live ok _
    obtain ⟨z,F,t,out,exec,paid,user,done,trace⟩ := finish x u S live ok
    exact ⟨z,F,t,x,out,exec,by simpa using paid,user,done,rfl,trace⟩
  | cons p ls ih =>
    intro unique
    obtain ⟨head,run⟩ := calls p
    obtain ⟨tail,rest⟩ := ih (List.nodup_cons.mp unique).2
    refine ⟨.seq head tail,?_⟩
    intro x u S live ok fresh
    obtain ⟨v,D,l,a,exec,paid,user,mid,step,valid,keep⟩ := run x u S live ok (fresh p List.mem_cons_self)
    obtain ⟨z,F,r,y,out,done,cost,same,rep,trace,restored⟩ := rest a v D mid valid (fun j hj =>
      keep j (fun eq => (List.nodup_cons.mp unique).1 (eq ▸ hj)) (fresh j (List.mem_cons_of_mem _ hj)))
    refine ⟨z,F,_,y,out,Exec.seq exec done,?_,same.trans user,rep,⟨a,step,trace⟩,restored⟩
    simpa only [Nat.cast_add,List.map_cons,List.sum_cons,add_assoc] using add_le_add paid cost

end IntegerMultBounds.MathlibTM2.M6.BitNode
