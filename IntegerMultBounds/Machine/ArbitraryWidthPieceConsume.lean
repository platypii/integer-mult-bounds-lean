import IntegerMultBounds.Machine.ArbitraryWidthLevelPlacement

/-! The concrete digit continuation: perform the runtime digit's selected
slice calls, erase that digit, then physically advance depth and power-width.
No callback execution trace is a hypothesis of this continuation theorem. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPieceConsume
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthConsumePlacement (S T parent emitted)
open ArbitraryWidthLevelPlacement (extras widthSlot)
open ArbitrarySliceCall (bank data)
open SharedPlacementAlphabet (setTape)

private theorem tail_width_update (root : Tapes ArbitrarySliceCall.rootCount prime)
    (ts bs cs : List Bool) (frame : Tapes 1 prime) :
    setTape (root.append (SliceHeaderPlacement.tail ts bs frame)) widthSlot
      (RadixZeroFill.encodedBinary cs) 1 = root.append (SliceHeaderPlacement.tail ts cs frame) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
      have hn : Fin.castAdd 12 i ≠ widthSlot := by
        intro he
        have hh := congrArg Fin.val he
        simp only [widthSlot,Fin.val_castAdd,Fin.val_natAdd,Fin.val_one] at hh
        have := i.isLt
        omega
      change Function.update _ widthSlot _ (Fin.castAdd 12 i) = _
      rw [Function.update_of_ne hn]
      simp only [Tapes.append,Fin.addCases_left]
  | right i =>
      by_cases hi : i = 1
      · subst i
        change Function.update _ widthSlot _ widthSlot = _
        rw [Function.update_self]
        simp only [Fin.addCases_right]
        rfl
      · have hn : Fin.natAdd ArbitrarySliceCall.rootCount i ≠ widthSlot := by
          intro he
          have hh := congrArg Fin.val he
          simp only [widthSlot,Fin.val_natAdd,Fin.val_one] at hh
          apply hi
          apply Fin.ext
          omega
        change Function.update _ widthSlot _ (Fin.natAdd ArbitrarySliceCall.rootCount i) = _
        rw [Function.update_of_ne hn]
        simp only [Tapes.append,Fin.addCases_right]
        fin_cases i <;> first | exact (hi rfl).elim | rfl

def program := seq (Placement.placed ArbitrarySliceRepeat.consume
  ArbitraryWidthConsumePlacement.repeatPlacement) ArbitraryWidthLevelPlacement.program

def cost (depth V b a : ℕ) (ts bs rs : List Bool) :=
  ArbitrarySliceRepeat.exactCost depth V b a ts bs rs+2*rs.length+6+120*125000^(depth+1)

theorem consumes (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool)
    (ns ts bs rs : List Bool) (t b a : ℕ) (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b) (ha : Counter.value rs = a)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+a*b ≤ v.width) (hw : b = 125000^depth)
    (hr : Shared50TapeGlobal.roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program
      (fun z => z = emitted ns rs (bank (data x) hs ts bs f p node scalar st frame) (extras 125000 depth))
      (fun z => z = parent ns
        (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
          (GrowingCounterData.advance (a*b) ts) (FixedBasePowerStep.bits 125000 (depth+1))
          f p node scalar st frame) (extras 125000 (depth+1)))
      (cost depth (volume prime v) b a ts bs rs) := by
  have hrepeat := ArbitrarySliceRepeat.repeat_hoare depth v hs ts bs rs t b a hp hv ht hb ha ct cb
    hfit hw hr f p node scalar st ready frame hfree x
  have hlocal := ArbitrarySliceRepeat.consume_hoare hrepeat
  have hrp := ArbitraryWidthConsumePlacement.repeat_placed ns rs
    (bank (data x) hs ts bs f p node scalar st frame)
    (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame)
    (extras 125000 depth) hlocal
  have hbs : bs = FixedBasePowerStep.bits 125000 depth :=
    BinaryCanonicalData.value_injective _ _ cb (FixedBasePowerStep.bits_canonical _ _)
      (by rw [FixedBasePowerStep.bits_value]; exact hb.trans hw)
  have hwidth : (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame).tape widthSlot =
      RadixZeroFill.encodedBinary (FixedBasePowerStep.bits 125000 depth) := by
    simp only [ArbitrarySliceCall.bank,widthSlot,Tapes.append,Fin.addCases_right]
    change RadixZeroFill.encodedBinary bs = _
    rw [hbs]
  have hhead : (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame).head widthSlot = 1 := by
    simp only [ArbitrarySliceCall.bank,widthSlot,Tapes.append,Fin.addCases_right]
    rfl
  have hl := ArbitraryWidthLevelPlacement.advances 125000 depth (by decide) ns
    (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame) hwidth hhead
  have he := tail_width_update
    (ArbitrarySliceCall.rootBank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs f p node scalar st)
    (GrowingCounterData.advance (a*b) ts) bs (FixedBasePowerStep.bits 125000 (depth+1)) frame
  change setTape (bank (data (ArbitrarySliceRepeat.images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame) widthSlot _ 1 = _ at he
  rw [he] at hl
  exact (hrp.seq hl).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem advance_bits (amount start : ℕ) :
    GrowingCounterData.advance amount (RecursiveChildQuotientsConstant.bits start) =
      RecursiveChildQuotientsConstant.bits (start+amount) :=
  BinaryCanonicalData.value_injective _ _
    (GrowingCounterData.advance_canonical _ _ (RecursiveChildQuotientsConstant.bits_canonical _))
    (RecursiveChildQuotientsConstant.bits_canonical _) (by
      rw [GrowingCounterData.advance_value,RecursiveChildQuotientsConstant.bits_value,
        RecursiveChildQuotientsConstant.bits_value])

theorem cost_bound (depth V t b a : ℕ) (ts bs rs : List Bool)
    (hV : 0 < V) (hbV : b ≤ V) (hfit : t+a*b ≤ V)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs) :
    cost depth V b a ts bs rs ≤
      a*(ArbitrarySliceStepBudget.budget depth V+6)+9*rs.length+34+120*125000^(depth+1) := by
  have hh := ArbitrarySliceRepeat.consumeCost_canonical depth V t b a ts bs rs hV hbV hfit ht hb ct cb
  unfold cost
  omega

end
end IntegerMultBounds.Machine.ArbitraryWidthPieceConsume
