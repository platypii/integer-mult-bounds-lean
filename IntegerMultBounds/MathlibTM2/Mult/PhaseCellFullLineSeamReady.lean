module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineInputFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamCropFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedClosedSeamRun

/-! Ordinary state facts needed by the full-period/seam execution, together
with the single frame used after bulk output is appended. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {T T' Q A s : ℕ} [NeZero s]

def seamReadPort (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
    (crops : SeamCropPlan T producer.result) (ks : List ℕ) (r : Fin T) : Prop :=
  r ∈ input.support ∨ (∃ i, producer.gridWork i = r) ∨
    r ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock,producer.result] ∨
    r ∈ crops.readPorts ks

structure SeamReady (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
    (crops : SeamCropPlan T producer.result) (p u l target t width : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (ks : List ℕ) (S : Stacks T A) : Prop where
  input : input.Ready p u l target t Fs S
  bank : ∀ i, S.R (producer.gridWork i) = []
  left : ∀ i, S.L (producer.gridWork (familyInverseCoreReg i)) = []
  controls : ∀ r ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock], S.R r = []
  crops : crops.Ready p s width Fs.length ks S
  result : S.R producer.result = []

theorem SeamReady.frame {input : FullLineInputPlan T} {producer : PackedProducerPlan T Q}
    {crops : SeamCropPlan T producer.result} {p u l target t width : ℕ}
    {Fs : List (ZMod s → GaussianInt)} {ks : List ℕ} {S F : Stacks T A}
    (ready : SeamReady input producer crops p u l target t width Fs ks S)
    (hleft : F.L = S.L)
    (hframe : ∀ r, seamReadPort input producer crops ks r → F.R r = S.R r) :
    SeamReady input producer crops p u l target t width Fs ks F := by
  have hcontrol (r : Fin T)
      (hr : r ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock,producer.result]) :=
    hframe r (Or.inr (Or.inr (Or.inl hr)))
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact ready.input.of_frame (by intro r hr; exact hframe r (Or.inl hr)) (by intro i; rw [hleft])
  · intro i; rw [hframe _ (Or.inr (Or.inl ⟨i,rfl⟩))]; exact ready.bank i
  · intro i; rw [hleft]; exact ready.left i
  · intro r hr
    rw [hcontrol r (by simp only [List.mem_cons] at hr ⊢; tauto)]
    exact ready.controls r hr
  · exact ready.crops.of_frame (by intro r hr; exact hframe r (Or.inr (Or.inr (Or.inr hr))))
  · rw [hcontrol _ (by simp)]; exact ready.result

/-- The exact output-only frame of the bulk execution preserves every seam
input, even when both programs append to the crop archive destination. -/
theorem SeamReady.after_output {input : FullLineInputPlan T} {producer : PackedProducerPlan T Q}
    {crops : SeamCropPlan T producer.result} {p u l target t width : ℕ}
    {Fs : List (ZMod s → GaussianInt)} {ks : List ℕ}
    (e : Fin T → Fin T') {S : Stacks T' A} (dst : Fin T') (word : List (Fin (A+4)))
    (hoff : ∀ r, seamReadPort input producer crops ks r → e r ≠ dst)
    (ready : SeamReady input producer crops p u l target t width Fs ks (embStk e S)) :
    SeamReady input producer crops p u l target t width Fs ks
      (embStk e {S with R := Function.update S.R dst (word++S.R dst)}) := by
  apply SeamReady.frame ready
  · rfl
  · intro r hr
    exact Function.update_of_ne (hoff r hr) _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan
