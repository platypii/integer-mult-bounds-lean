module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceConsume
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceRepeatWithin

/-! A physical digit continuation shares one reserve across repeated slices,
digit erasure, and the actual depth/width advance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceConsumeWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthConsumePlacement (S T parent emitted)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthLevelPlacement (extras widthSlot)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall (bank data)
open SharedPlacementAlphabet (setTape)

open ArbitraryWidthPieceConsume

def coefficient : ℕ := max ArbitrarySliceRepeatWithin.coefficient (120*Machine.width+1)

theorem consumes_within (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool)
    (ns ts bs rs : List Bool) (t b a : ℕ) (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b) (ha : Counter.value rs = a)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (ca : GrowingCounterData.Canonical rs) (hbV : b ≤ volume prime v)
    (hfit : t+a*b ≤ v.width) (hw : b = Machine.width^depth)
    (hr : roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime v : ℕ) ≤
      (emitted ns rs (bank (data x) hs ts bs f p node scalar st frame) (extras Machine.width depth)).head j ∧
      (emitted ns rs (bank (data x) hs ts bs f p node scalar st frame) (extras Machine.width depth)).head j+
        (coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin program
      (fun z => z = emitted ns rs (bank (data x) hs ts bs f p node scalar st frame) (extras Machine.width depth))
      (fun z => z = parent ns
        (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
          (GrowingCounterData.advance (a*b) ts) (FixedBasePowerStep.bits Machine.width (depth+1))
          f p node scalar st frame) (extras Machine.width (depth+1)))
      (cost depth (volume prime v) b a ts bs rs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let before := bank (data x) hs ts bs f p node scalar st frame
  let after := bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
    (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame
  let level := extras Machine.width depth
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hR := Nat.mul_le_mul_right (volume prime v)
    (show ArbitrarySliceRepeatWithin.coefficient ≤ coefficient from le_max_left _ _)
  have hrepeat := ArbitrarySliceRepeatWithin.consume_within depth v hs ts bs rs t b a hp hv ht hb ha ct cb ca
    hfit hw hr f p node scalar st ready frame hfree x lo hi (by
      intro j
      have hm := hmargin (ArbitraryWidthConsumePlacement.repeatPlacement (Fin.castAdd 18 j))
      change lo+(coefficient*volume prime v : ℕ) ≤
        (Placement.active ArbitraryWidthConsumePlacement.repeatPlacement (emitted ns rs before level)).head j ∧
        (Placement.active ArbitraryWidthConsumePlacement.repeatPlacement (emitted ns rs before level)).head j+
          (coefficient*volume prime v : ℕ) ≤ hi at hm
      rw [ArbitraryWidthConsumePlacement.repeat_active] at hm
      dsimp only [before] at hm
      omega)
  have hrp := ArbitraryWidthConsumePlacement.repeat_placed_within ns rs before after level lo hi hrepeat (by
    intro j
    have hm := hmargin j
    change lo ≤ (emitted ns rs before level).head j ∧ (emitted ns rs before level).head j ≤ hi
    dsimp only [before,level]
    omega)
  have hbs : bs = FixedBasePowerStep.bits Machine.width depth :=
    BinaryCanonicalData.value_injective _ _ cb (FixedBasePowerStep.bits_canonical _ _)
      (by rw [FixedBasePowerStep.bits_value]; exact hb.trans hw)
  have hwidth : (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame).tape widthSlot =
      RadixZeroFill.encodedBinary (FixedBasePowerStep.bits Machine.width depth) := by
    simp only [ArbitrarySliceCall.bank,widthSlot,Tapes.append,Fin.addCases_right]
    change RadixZeroFill.encodedBinary bs = _
    rw [hbs]
  have hhead : (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame).head widthSlot = 1 := by
    simp only [ArbitrarySliceCall.bank,widthSlot,Tapes.append,Fin.addCases_right]
    rfl
  have hl := ArbitraryWidthLevelPlacement.advances Machine.width depth two_le_width ns
    (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame) hwidth hhead
  have hhead := ArbitrarySliceCallWithin.bank_offset_head_eq (ArbitrarySliceRepeat.images v t b a hfit x) x
    hs (GrowingCounterData.advance (a*b) ts) bs ts bs f p node scalar st frame
  have hclose := ArbitraryWidthConsumePlacement.parent_emitted_heads ns rs before after level hhead
  have hbudget : 120*Machine.width^(depth+1)+1 ≤ coefficient*volume prime v := by
    have hmul := Nat.mul_le_mul_left (120*Machine.width) hbV
    have hc := Nat.mul_le_mul_right (volume prime v)
      (show 120*Machine.width+1 ≤ coefficient from le_max_right _ _)
    rw [pow_succ,← hw]
    nlinarith only [hmul,hc,hV]
  have hwl := HoareWithin.of_time_heads hl lo hi (by
    rintro w rfl j
    have hm := hmargin j
    have hh := hclose j
    change lo+(120*Machine.width^(depth+1) : ℕ) ≤ (parent ns after level).head j ∧
      (parent ns after level).head j+(120*Machine.width^(depth+1) : ℕ) ≤ hi
    dsimp only [before,after,level] at hh ⊢
    omega)
  have hfull := hrp.seq hwl
  apply HoareWithin.of_time_invariant (consumes depth v hs ns ts bs rs t b a hp hv ht hb ha ct cb
    hfit hw hr f p node scalar st ready frame hfree x)
  intro c hc
  exact hfull.invariant hc

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceConsumeWithin
