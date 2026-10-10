import IntegerMultBounds.Machine.AllAxisNativePolynomialData

/-! One fixed original-input aggregate phase caller physically copies native
headers and immutable ell, synthesizes stage metadata, executes the actual
finite edge dispatcher on the original native source and erases every phase
header/work tape. No prepared header, codec or execution callback is assumed. -/
namespace IntegerMultBounds.Machine.AllAxisNativePolynomialCaller
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows)
open AllAxisPolynomialTensorResult (flatten)
open AllAxisNativePolynomialData (result source)
open AllAxisPhaseOriginalScalar (caller outer words)
open ActivePrefixStageHeadersData (Order)
open CompactAllAxisPhaseDispatch (count edge)
open Networks.ComplexPhaseRowSchedule (dimension)
open SharedPlacementAlphabet (setTape sharedPlacement)
variable {s : Shape}

def call (pc : Fin count) := Placement.placed
  (Alphabet.program (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha) (CompactAllAxisPhaseDispatch.call pc))
  (sharedPlacement source (56 : Fin 67))
def program (order : Order) (pc : Fin count) :=
  seq (AllAxisPhaseOriginalMetadata.setup order) (seq (call pc) AllAxisPhaseOriginalMetadata.cleanup)

def cost (order : Order) (d : Inputs s) (pc : Fin count) (ell w : ℕ) :=
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (words d ell)+1+
    ActivePrefixStageHeadersRun.cost order d.stage d.rows+1+
    (2*count+3+AllAxisPolynomialNative.cost order d.stage d.rows (dimension (edge pc)) ell w)+1+
    (AllAxisPhaseStageMetadata.cleanupCost order d.stage d.rows+1+
      FixedHeaderBankCopy.cleanupCost (t:=outer) (words d ell))

theorem call_runs (order : Order) (d : Inputs s) (hslots : d.stage.slots=25^3)
    (pc : Fin count) (hm : 0<dimension (edge pc)) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    HoareTime (call pc)
      (fun z => z=(caller d (rows d xs hw) ell).append (AllAxisPhaseOriginalMetadata.ready order d ell))
      (fun z => z=(caller d (rows d (result d ell (dimension (edge pc))
        (CompactComplexPhaseControlCodec.weights (edge pc)).reverse xs)
          (AllAxisNativePolynomialData.result_width d ell (dimension (edge pc)) w
            (CompactComplexPhaseControlCodec.weights (edge pc)).reverse xs hw)) ell).append
        (AllAxisPhaseOriginalMetadata.ready order d ell))
      (2*count+3+AllAxisPolynomialNative.cost order d.stage d.rows (dimension (edge pc)) ell w) := by
  let m := dimension (edge pc)
  let ws := (CompactComplexPhaseControlCodec.weights (edge pc)).reverse
  let x := flatten d ell xs
  have h0 := AllAxisPolynomialActual.runs d hslots pc hm order ell w x
    (AllAxisPolynomialTensorResult.flatten_width d ell w xs hw)
  have h1 : HoareTime
      (Alphabet.program (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha) (CompactAllAxisPhaseDispatch.call pc))
      (fun z => z=Alphabet.mapTapes (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha)
        (AllAxisPolynomialPlacement.input order d.stage d.rows ell x))
      (fun z => z=Alphabet.mapTapes (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha)
        (AllAxisPolynomialPlacement.output order d.stage d.rows m ws ell x))
      (2*count+3+AllAxisPolynomialNative.cost order d.stage d.rows m ell w) := by
    apply (Alphabet.map_hoare (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha) h0).consequence _ _ le_rfl
    · rintro z rfl; exact ⟨_,rfl,rfl⟩
    · rintro z ⟨b,rfl,rfl⟩; rfl
  have h2 := SharedPlacementAlphabet.shared_hoare h1 (caller d (rows d xs hw) ell) source
    (56 : Fin 67) (fun _ => blank) 0
    (AllAxisNativePolynomialData.source_word d ell w xs hw)
    (AllAxisNativePolynomialData.source_head d ell w xs hw)
  have hc := AllAxisPolynomialPlacement.mapped_cleared_output ActivePrefixStageNative.ha
    order d.stage d.rows m ws ell x
  have hs := AllAxisPolynomialPlacement.output_source ActivePrefixStageNative.ha
    order d.stage d.rows m ws ell x
  rw [hc,←AllAxisPhasePreparedBridge.ready_eq order d ell x,hs.1,hs.2] at h2
  dsimp only [x] at h2
  rw [AllAxisNativePolynomialData.flatten_result,AllAxisNativePolynomialData.replace_rows d ell w xs _ hw
    (AllAxisNativePolynomialData.result_width d ell m w ws xs hw)] at h2
  exact h2

def input (d : Inputs s) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    Tapes (outer+67) Networks.Shared50ModularControl.prime :=
  (caller d (rows d xs hw) ell).append (FixedHeaderBankCopy.empty 67)
def output (d : Inputs s) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    Tapes (outer+67) Networks.Shared50ModularControl.prime :=
  (caller d (rows d (result d ell (dimension (edge pc))
      (CompactComplexPhaseControlCodec.weights (edge pc)).reverse xs)
    (AllAxisNativePolynomialData.result_width d ell (dimension (edge pc)) w
      (CompactComplexPhaseControlCodec.weights (edge pc)).reverse xs hw)) ell).append
    (FixedHeaderBankCopy.empty 67)

theorem runs (order : Order) (d : Inputs s) (hslots : d.stage.slots=25^3)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage)
    (pc : Fin count) (hm : 0<dimension (edge pc)) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    HoareTime (program order pc)
      (fun z => z=input d ell w xs hw)
      (fun z => z=output d pc ell w xs hw) (cost order d pc ell w) := by
  have hsetup := AllAxisPhaseOriginalMetadata.setup_runs order d (rows d xs hw) ell ho
  have hcall := call_runs order d hslots pc hm ell w xs hw
  have hcleanup := AllAxisPhaseOriginalMetadata.cleanup_runs order d
    (rows d (result d ell (dimension (edge pc)) (CompactComplexPhaseControlCodec.weights (edge pc)).reverse xs)
      (AllAxisNativePolynomialData.result_width d ell (dimension (edge pc)) w
        (CompactComplexPhaseControlCodec.weights (edge pc)).reverse xs hw)) ell
  have h := hsetup.seq (hcall.seq hcleanup)
  simpa only [program,input,output,cost,Nat.add_assoc] using h



theorem call_zero_runs (order : Order) (d : Inputs s) (pc : Fin count)
    (hm : dimension (edge pc)=0) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    HoareTime (call pc)
      (fun z => z=(caller d (rows d xs hw) ell).append (AllAxisPhaseOriginalMetadata.ready order d ell))
      (fun z => z=(caller d (rows d xs hw) ell).append (AllAxisPhaseOriginalMetadata.ready order d ell))
      (2*count+3) := by
  let x := flatten d ell xs
  let b := AllAxisPolynomialStreamInit.input order d.stage d.rows
    (AllAxisPolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 x) ell
  have h0 := CompactAllAxisPhaseDispatch.call_zero_runs pc hm b
  have h1 : HoareTime
      (Alphabet.program (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha) (CompactAllAxisPhaseDispatch.call pc))
      (fun z => z=Alphabet.mapTapes (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha)
        (AllAxisPolynomialPlacement.input order d.stage d.rows ell x))
      (fun z => z=Alphabet.mapTapes (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha)
        (AllAxisPolynomialPlacement.input order d.stage d.rows ell x)) (2*count+3) := by
    apply (Alphabet.map_hoare (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha) h0).consequence _ _ le_rfl
    · rintro z rfl; exact ⟨_,rfl,rfl⟩
    · rintro z ⟨u,rfl,rfl⟩; rfl
  have hs := AllAxisNativePolynomialData.source_word d ell w xs hw
  have hh := AllAxisNativePolynomialData.source_head d ell w xs hw
  have h2 := SharedPlacementAlphabet.shared_hoare h1 (caller d (rows d xs hw) ell) source
    (56 : Fin 67) (fun _ => blank) 0 hs hh
  have hf :
      (Alphabet.mapTapes (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha)
        (AllAxisPolynomialPlacement.input order d.stage d.rows ell x)).tape 56=
      SymbolTriplePlaced.mapTape ActivePrefixStageNative.ha
        (putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized x)) ∧
      (Alphabet.mapTapes (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha)
        (AllAxisPolynomialPlacement.input order d.stage d.rows ell x)).head 56=0 := ⟨rfl,rfl⟩
  have he : setTape (caller d (rows d xs hw) ell) source
      ((Alphabet.mapTapes (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha)
        (AllAxisPolynomialPlacement.input order d.stage d.rows ell x)).tape 56)
      ((Alphabet.mapTapes (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha)
        (AllAxisPolynomialPlacement.input order d.stage d.rows ell x)).head 56)=
      caller d (rows d xs hw) ell := by
    rw [hf.1,hf.2,←hs,←hh,SharedPlacementAlphabet.setTape_self]
  rwa [he,←AllAxisPhasePreparedBridge.ready_eq order d ell x] at h2

def zeroCost (order : Order) (d : Inputs s) (ell : ℕ) :=
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (words d ell)+1+
    ActivePrefixStageHeadersRun.cost order d.stage d.rows+1+(2*count+3)+1+
    (AllAxisPhaseStageMetadata.cleanupCost order d.stage d.rows+1+
      FixedHeaderBankCopy.cleanupCost (t:=outer) (words d ell))

theorem zero_runs (order : Order) (d : Inputs s)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage)
    (pc : Fin count) (hm : dimension (edge pc)=0) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    HoareTime (program order pc) (fun z => z=input d ell w xs hw)
      (fun z => z=input d ell w xs hw) (zeroCost order d ell) := by
  have hsetup := AllAxisPhaseOriginalMetadata.setup_runs order d (rows d xs hw) ell ho
  have hcall := call_zero_runs order d pc hm ell w xs hw
  have hcleanup := AllAxisPhaseOriginalMetadata.cleanup_runs order d (rows d xs hw) ell
  simpa only [program,input,zeroCost,Nat.add_assoc] using hsetup.seq (hcall.seq hcleanup)


theorem zero_cost_bound (order : Order) (d : Inputs s)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) (ell : ℕ) (hR : 2^ell≤s.payload) :
    zeroCost order d ell≤(804273+2*count)*(d.rows*s.recordWidth) := by
  have hh := AllAxisPhaseOriginalMetadata.lifecycle_bound order d ell ho hR
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hr := d.hr
  have hV : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  have hn : 2*count+5≤(2*count+5)*(d.rows*s.recordWidth) := by
    exact Nat.le_mul_of_pos_right _ hV
  unfold zeroCost
  nlinarith

/-- Every descriptor lifecycle and actual dispatch/overwrite transition is paid. -/
theorem cost_bound (order : Order) (d : Inputs s) (hslots : d.stage.slots=25^3)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage)
    (pc : Fin count) (hm : 0<dimension (edge pc)) (ell w : ℕ) (hR : 2^ell≤s.payload) :
    cost order d pc ell w≤804270*(d.rows*s.recordWidth)+
      (d.rows*2^s.bits)*(((2*FixedBasePowerDescriptor.constant 2+15000)+(2*count+3))*s.payload+34*2^ell*w) := by
  have hh := AllAxisPhaseOriginalMetadata.lifecycle_bound order d ell ho hR
  have hp := AllAxisPolynomialActual.volume_bound d hslots pc hm order ell w hR
  have hpay : 0<s.payload := by have := d.hrecord; omega
  have hr := d.hr
  have hV : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  unfold cost
  omega

theorem cost_linear (order : Order) (d : Inputs s) (hslots : d.stage.slots=25^3)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage)
    (pc : Fin count) (hm : 0<dimension (edge pc)) (ell w : ℕ)
    (hR : 2^ell≤s.payload) (hw : 2^ell*w≤s.payload) :
    cost order d pc ell w≤(804304+(2*FixedBasePowerDescriptor.constant 2+15000)+(2*count+3))*
      (d.rows*s.recordWidth) := by
  have h := cost_bound order d hslots ho pc hm ell w hR
  have hw' : 34*2^ell*w≤34*s.payload := by nlinarith
  have hp := Nat.mul_le_mul_left (d.rows*2^s.bits)
    (Nat.add_le_add_left hw' (((2*FixedBasePowerDescriptor.constant 2+15000)+(2*count+3))*s.payload))
  have hV : d.rows*s.recordWidth=(d.rows*2^s.bits)*s.payload := by
    simp only [Shape.recordWidth,Nat.mul_assoc]
  rw [hV] at h ⊢
  nlinarith

end
end IntegerMultBounds.Machine.AllAxisNativePolynomialCaller
