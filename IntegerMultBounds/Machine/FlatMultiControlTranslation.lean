import IntegerMultBounds.Machine.MultiControlPrefixTranslationInit
import IntegerMultBounds.Machine.FlatControlledShift

/-! Concrete flat-array multi-control translation. Fibers are extracted from the
array, all prefix fields are physically generated and enumerated, and each fixed
rational expression is evaluated on the actual radix slices of the fiber index.
No supplied family of addresses, offsets, or refreshed source copies is assumed. -/
namespace IntegerMultBounds.Machine.FlatMultiControlTranslation

open RadixLinearCombinationRefresh (Expr leaves)
open PrefixCounterInitPlacement (handoff extras)
variable {c radix B : ℕ} [Fact radix.Prime]

/-- Canonical coordinate slice in the least-significant-first control order. -/
def coordinate (b i : ℕ) (j : Fin c) : ℕ := (i/radix^(j.val*b))%radix^b

/-- Mathematical rational expression on the concrete flat prefix index. -/
def evaluate (b i : ℕ) : Expr c → ZMod (radix^b)
  | .term j r => Swap.Modular.ratMod (radix^b) r * (coordinate (radix := radix) b i j : ZMod (radix^b))
  | .add l r => evaluate b i l+evaluate b i r

def physicalOffset (e : Expr c) (b i : ℕ) : ℕ := (evaluate (radix := radix) b i e).val

private theorem split_order (j : Fin c) :
    (List.finRange c).take j.val ++ j::(List.finRange c).drop (j.val+1) = List.finRange c := by
  have hh : j.val < (List.finRange c).length := by simpa only [List.length_finRange] using j.isLt
  have hd : j::(List.finRange c).drop (j.val+1) = (List.finRange c).drop j.val := by
    simpa using List.getElem_cons_drop hh
  rw [hd,List.take_append_drop]

private theorem widthSum_const (order : List (Fin c)) (b : ℕ) :
    PrefixAddressData.widthSum order (fun _ => b) = order.length*b := by
  induction order with
  | nil => simp [PrefixAddressData.widthSum]
  | cons j order ih => simp [PrefixAddressData.widthSum] at ih ⊢; nlinarith

/-- The field used by the executing counter equals the concrete prefix-index
slice, including all lower-order controls in the divisor. -/
theorem control_coordinate (b i : ℕ) (hi : i < radix^(c*b)) (j : Fin c) :
    RadixDigits.value (MultiControlPrefixTranslationStream.fields (List.finRange c)
      (MultiControlPrefixTranslationInit.initial (radix := radix) b) i j) = coordinate (radix := radix) b i j := by
  let low := (List.finRange c).take j.val
  let high := (List.finRange c).drop (j.val+1)
  have hs : low++j::high = List.finRange c := split_order j
  have hn : (low++j::high).Nodup := by rw [hs]; exact List.nodup_finRange c
  have hwidth : PrefixAddressData.widthSum (low++j::high) (fun _ => b) = c*b := by
    rw [hs,widthSum_const,List.length_finRange]
  have hl : PrefixAddressData.widthSum low (fun _ => b) = j.val*b := by
    rw [widthSum_const]
    simp [low,List.length_take]
  have hh := PrefixAddressData.enumeration_selected (Fact.out : radix.Prime).two_le low high j hn
    (fun _ => b) i (by simpa only [hwidth] using hi)
  rw [hs,hl] at hh
  exact hh

private theorem evaluate_eq (e : Expr c) (seed : Fin c) (b i : ℕ) (hi : i < radix^(c*b)) :
    RadixLinearCombination.valueMod b e.erase
      (RadixLinearCombinationShared.read seed (MultiControlPrefixTranslationStream.fields (List.finRange c)
        (MultiControlPrefixTranslationInit.initial (radix := radix) b) i)) = evaluate (radix := radix) b i e := by
  induction e with
  | term j r =>
    simp only [Expr.erase,RadixLinearCombination.valueMod,RadixLinearCombinationShared.read_at,evaluate]
    rw [control_coordinate b i hi j]
  | add l r hl hr => simp only [Expr.erase,RadixLinearCombination.valueMod,evaluate,hl,hr]

/-- Equality of the physically used canonical offset with the actual modular
rational expression on the flat prefix coordinate. -/
theorem offset_eq (e : Expr c) (he : RadixLinearCombination.Valid (q := radix) e.erase)
    (seed : Fin c) (b i : ℕ) (hi : i < radix^(c*b)) :
    MultiControlPrefixTranslationStream.offset e seed (List.finRange c)
      (MultiControlPrefixTranslationInit.initial (radix := radix) b) i = physicalOffset (radix := radix) e b i := by
  have hh := MultiControlPrefixTranslationStream.offset_value e he seed (List.finRange c)
    (MultiControlPrefixTranslationInit.initial (radix := radix) b) b i (MultiControlPrefixTranslationInit.initial_length b)
  rw [evaluate_eq e seed b i hi] at hh
  have hw := RadixLinearCombinationShared.read_width seed
    (MultiControlPrefixTranslationStream.fields (List.finRange c) (MultiControlPrefixTranslationInit.initial (radix := radix) b) i) b
    (fun j => (MultiControlPrefixTranslationStream.fields_length _ _ i j).trans
      (MultiControlPrefixTranslationInit.initial_length b j))
  have hb := RadixLinearCombinationBinary.bits_lt e.erase _ b hw
  change MultiControlPrefixTranslationStream.offset e seed (List.finRange c)
    (MultiControlPrefixTranslationInit.initial (radix := radix) b) i < radix^b at hb
  have hp : 0 < radix^b := pow_pos (Fact.out : radix.Prime).pos b
  let : NeZero (radix^b) := ⟨by omega⟩
  have hv := congrArg ZMod.val hh
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hb,physicalOffset] using hv

/-- Actual source array, split into fibers by the verified row-major constructor. -/
def input (e : Expr c) (seed : Fin c) (b : ℕ) (ws : Fin c → List Bool)
    (a : Fin (radix^(c*b)*(radix^b*B)) → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :=
  MultiControlPrefixTranslationInit.input (radix := radix) e seed b (radix^(c*b)) ws source dest p q bs qs ns (FlatControlledShift.payload a)

def output (e : Expr c) (seed : Fin c) (b : ℕ) (ws : Fin c → List Bool)
    (a : Fin (radix^(c*b)*(radix^b*B)) → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :=
  MultiControlPrefixTranslationInit.output (radix := radix) e seed b B (radix^(c*b)) ws source dest p q bs qs ns (FlatControlledShift.payload a)

omit [Fact radix.Prime] in
/-- Concatenating the machine's supplied fibers is literally the flat input. -/
theorem source_array (b : ℕ) (a : Fin (radix^(c*b)*(radix^b*B)) → Fin 4) :
    (TranslationStream.fibers (radix^b) (radix^(c*b)) (FlatControlledShift.payload a)).flatten = List.ofFn a :=
  FlatControlledShift.source_eq a

private def bodyDestination (e : Expr c) : Fin (MultiControlPrefixTranslationBootstrap.TapeCount e) :=
  Fin.castAdd 2 (Fin.natAdd (MultiControlTranslationExecution.ArithmeticTapes e) (11 : Fin 12))

/-- Real destination tape after the initializer's static whole-bank placement. -/
def destinationSlot (e : Expr c) :=
  handoff (MultiControlPrefixTranslationInit.streamPlacement e) (Fin.castAdd (extras c) (bodyDestination e))

theorem destination_tape (e : Expr c) (he : RadixLinearCombination.Valid (q := radix) e.erase)
    (seed : Fin c) (b : ℕ) (ws : Fin c → List Bool)
    (a : Fin (radix^(c*b)*(radix^b*B)) → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    (output e seed b ws a source dest p q bs qs ns).tape (destinationSlot e) =
      fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord dest q (FiberLayoutData.translated a (fun i => physicalOffset (radix := radix) e b i.val)) z) := by
  change (Placement.active (handoff (MultiControlPrefixTranslationInit.streamPlacement e))
    (MultiControlPrefixTranslationInit.output (radix := radix) e seed b B (radix^(c*b)) ws source dest p q bs qs ns (FlatControlledShift.payload a))).tape
    (bodyDestination e) = _
  rw [MultiControlPrefixTranslationInit.output_active]
  simp only [MultiControlPrefixTranslationInit.streamOutput,CountedLoopReuseAlphabet.bank,bodyDestination,Tapes.append,Fin.addCases_left]
  rw [MultiControlPrefixTranslationStream.state_destination]
  unfold MultiControlPrefixTranslationStream.outputPrefix
  rw [FlatControlledShift.output_eq]
  have hoff : (fun i : Fin (radix^(c*b)) => MultiControlPrefixTranslationStream.offset e seed (List.finRange c)
      (MultiControlPrefixTranslationInit.initial (radix := radix) b) i.val) =
      (fun i => physicalOffset (radix := radix) e b i.val) := by
    funext i
    exact offset_eq e he seed b i.val i.isLt
  rw [hoff]

/-- Every suffix symbol moves to the actual computed modular target address. -/
theorem output_symbol (e : Expr c) (he : RadixLinearCombination.Valid (q := radix) e.erase)
    (seed : Fin c) (b : ℕ) (ws : Fin c → List Bool)
    (a : Fin (radix^(c*b)*(radix^b*B)) → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (i : Fin (radix^(c*b))) (y : Fin (radix^b)) (j : Fin B) :
    (output e seed b ws a source dest p q bs qs ns).tape (destinationSlot e)
      (q+((i.val*(radix^b*B)+((y.val+physicalOffset (radix := radix) e b i.val)%radix^b)*B+j.val : ℕ) : ℤ)) =
      (RadixToBinary.binaryEncoding (q := radix)).encode (a (FiberLayoutData.index i y j)) := by
  rw [destination_tape e he seed b ws a source dest p q bs qs ns]
  have hh := FiberLayoutData.translated_entry a (fun i => physicalOffset (radix := radix) e b i.val) i y j
  obtain ⟨hj,hv⟩ := List.getElem?_eq_some_iff.mp hh
  dsimp only
  rw [WordSegments.get _ _ _ _ hj,hv]

/-- Complete actual flat-array execution, including zero-field generation,
blank-workspace setup, arithmetic, carries, payload movement and all cleanup. -/
theorem realizes_hoare (e : Expr c) (he : RadixLinearCombination.Valid (q := radix) e.erase)
    (seed : Fin c) (b : ℕ) (hB : 0 < B) (ws : Fin c → List Bool)
    (hw : ∀ j, Counter.value (ws j) = b) (cw : ∀ j, GrowingCounterData.Canonical (ws j))
    (a : Fin (radix^(c*b)*(radix^b*B)) → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b) (hn : Counter.value ns = radix^(c*b))
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (MultiControlPrefixTranslationInit.program (radix := radix) e seed)
      (fun v => v = input e seed b ws a source dest p q bs qs ns)
      (fun v => v = output e seed b ws a source dest p q bs qs ns ∧
        ∀ (i : Fin (radix^(c*b))) (y : Fin (radix^b)) (j : Fin B),
          v.tape (destinationSlot e)
            (q+((i.val*(radix^b*B)+((y.val+physicalOffset (radix := radix) e b i.val)%radix^b)*B+j.val : ℕ) : ℤ)) =
              (RadixToBinary.binaryEncoding (q := radix)).encode (a (FiberLayoutData.index i y j)))
      ((28*leaves e+2*RadixLinearCombination.linearConstant e.erase+594+33*c)*(radix^(c*b)*(radix^b*B))) := by
  have hh := MultiControlPrefixTranslationInit.full_cycle_hoare_linear e seed hB ws hw cw source dest p q bs qs ns rfl
    hb hq hn cb cq cn (FlatControlledShift.payload a) (FlatControlledShift.payload_length a)
  apply hh.consequence (fun _ h => h) _ _
  · rintro v rfl
    exact ⟨rfl,fun i y j => output_symbol e he seed b ws a source dest p q bs qs ns i y j⟩
  · rw [source_array,List.length_ofFn]

end IntegerMultBounds.Machine.FlatMultiControlTranslation
