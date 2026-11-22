module

public import IntegerMultBounds.MathlibTM2.M6.BitPhaseRun

/-! Read each borrowed label independently across the physical COPY schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589
open Cover M8.RevMachine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩
open RecursiveInterchangeLayout (volume)

noncomputable def borrowedRead {w B K : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
    (data : Fin 142081 → Fin (volume prime (copyLabelLayout w B K)) → ZMod 2) :
    ℕ → AddressStream (ZMod (prime^w)) :=
  Copy.extendStored fun i s => chartRead (data (ownerTape n r d i)) g {z with a := copyActive s}

/-- Routing every register into its scatter chart and back executes the
literal scatter separately at every label, for arbitrary dirty input. -/
theorem borrowedScatter_read {w B K : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    {x entered scattered y : Fin 142081 → Fin (volume prime (copyLabelLayout w B K)) → ZMod 2}
    (entry : ∀ i : Fin 661, LabelPermutation.Transport (copyLabelLayout w B K) B w
      (fun g => g*registerChart w n i.val) (ext (x (ownerTape n r d i))) (ext (entered (ownerTape n r d i))))
    (effect : CopyScheduleEffect n r d w B K Copy.lifecycles entered scattered)
    (exitRoute : ∀ i : Fin 661, LabelPermutation.Transport (copyLabelLayout w B K) B w
      (fun g => g*(registerChart w n i.val).transpose) (ext (scattered (ownerTape n r d i))) (ext (y (ownerTape n r d i))))
    (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B) (i : Fin 661) :
    let frame := fun j => selectedFrame w (Frames.beforeScatter j)
    borrowedRead n r d g z y i.val = frame i.val (FramedCircuit.moduleRun
      (sectionscatter.map RawGate.toCircuit) (FramedCircuit.decode frame (borrowedRead n r d g z x)) i.val) := by
  have input : scatterRead n r d g z entered = borrowedRead n r d g z x := by
    apply congrArg Copy.extendStored
    funext j s
    exact congrFun (chartRead_transport (entry j) g) _
  have output := chartRead_transport (exitRoute i) (g*registerChart w n i.val)
  rw [Matrix.mul_assoc,mul_eq_one_comm.mp (registerChart_inverse w n i.val),Matrix.mul_one] at output
  have read := scatterRead_endpoint effect g z i
  dsimp only at read ⊢
  rw [input] at read
  refine Eq.trans ?_ read
  funext s
  simpa only [borrowedRead,scatterRead,Copy.extendStored,dite_eq_left i.isLt] using
    congrFun output {z with a := copyActive s}

/-- Move the entire live register bank into or out of its scatter charts.
The same block serves every atom width and every batch size. -/
theorem borrowedRoute_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) (enter : Bool) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
    let v := copyLabelLayout w B K
    let V := volume prime v
    ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := v)),
      stage.cost ≤ C*V + 661*(252*LeafCore.coreCost V (w*64)+1) ∧
      (∀ x (i : Fin 661), let A := registerChart w n i.val
        LabelPermutation.Transport v B w (fun g => g*(if enter then A.transpose else A))
          (ext (x (ownerTape n r d i))) (ext (stage.transform x (ownerTape n r d i)))) ∧
      ∀ x k, (∀ i, ownerTape n r d i ≠ k) → stage.transform x k = x k := by
  let io := (⟨ownerTape n r d,ownerTape_injective n r d⟩ : Fin 661 ↪ Fin 142081)
  obtain ⟨block,C,leading,runs⟩ := ownerChartRoutes io n enter (List.finRange 661) (List.nodup_finRange _)
  refine ⟨C,?_⟩
  intro w B K hw hb hk v V
  have hp := Shared50ModularControl.prime_prime.pos
  have positive : v.Positive := by
    dsimp [v,copyLabelLayout,RecursiveInterchangeLayout.Descriptor.Positive]
    exact ⟨by positivity,by decide,by positivity,by decide,hk⟩
  let result := runs v w B hw hb rfl positive
  let bank := fun x => SharedBankStageInput.raw
    (LabelCall.bank (copyOwners (T := 142081) (v := v) x) v (M8.Stage2Machine.Straight.words (LabelSchedule.base v w))) block.tapes
  let slots := fun i : Fin 142081 => block.slots (Fin.castAdd 24 i)
  refine ⟨{ tapes := _, states := _, program := block.program, transform := fun x => (result x).choose,
            input := bank, output := fun x => bank (result x).choose, slots := slots,
            slots_injective := block.slots_injective.comp (Fin.castAdd_injective _ _),
            metadata := SharedBank.strip (bank 0) slots, cost := C*V+661*(252*LeafCore.coreCost V (w*64)+1),
            input_payload := fun _ => copyRoute_payload block leading _ _ _,
            output_payload := fun _ => copyRoute_payload block leading _ _ _,
            strip_input := fun _ => routePrivate block leading _ _ _ _,
            realizes := fun x => by simpa only [List.length_finRange] using (result x).choose_spec.2.2 },
          le_rfl,fun x i => (result x).choose_spec.1 i (List.mem_finRange _),?_⟩
  intro x k off
  exact (result x).choose_spec.2.1 k (by
    rintro h
    obtain ⟨i,_,eqn⟩ := List.mem_map.mp h
    exact off i eqn)

/-- One charged stage executes all COPY windows on independent borrowed rows. -/
theorem borrowedScatter_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
    let v := copyLabelLayout w B K
    let V := volume prime v
    let W := B*prime^(64*(w*64))*K
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
    ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := v)),
      stage.cost ≤ C*V + (2*(63*9+252*527)+1322*252)*LeafCore.coreCost V (w*64) +
        9*engine.time (copyChild w W) hs + 1333 ∧
      (∀ x g z (i : Fin 661), let frame := fun j => selectedFrame w (Frames.beforeScatter j)
        borrowedRead n r d g z (stage.transform x) i.val = frame i.val (FramedCircuit.moduleRun
          (sectionscatter.map RawGate.toCircuit) (FramedCircuit.decode frame (borrowedRead n r d g z x)) i.val)) ∧
      ∀ x k, k ≠ Fin.last 142080 → (∀ i, ownerTape n r d i ≠ k) → stage.transform x k = x k := by
  obtain ⟨C,entry⟩ := borrowedRoute_stage n r d false
  obtain ⟨D,scatter⟩ := routedCopy_schedule n r d engine
  obtain ⟨F,back⟩ := borrowedRoute_stage n r d true
  refine ⟨C+D+F,?_⟩
  intro w B K hw hb hk v V W hs
  obtain ⟨a,ac,enters,aOff⟩ := entry w B K hw hb hk
  obtain ⟨b,acts,bc⟩ := scatter w B K hw hb hk
  obtain ⟨f,fc,leaves,fOff⟩ := back w B K hw hb hk
  refine ⟨SharedBankStage.compose (SharedBankStage.compose a b) f,?_,?_,?_⟩
  · change a.cost+b.cost+1+f.cost+1 ≤ _
    apply (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add ac bc) 1) fc) 1).trans
    dsimp only [V,W,hs,v]
    exact Nat.le_of_eq (by ring)
  · intro x g z i
    exact borrowedScatter_read n r d (enters x) (acts _) (leaves _) g z i
  · intro x k live off
    exact (fOff _ _ off).trans ((copySchedule_other (acts _) k live off).trans (aOff _ _ off))

end IntegerMultBounds.MathlibTM2.M6.BitNode
