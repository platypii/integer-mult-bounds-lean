import IntegerMultBounds.Machine.MultiControlTranslationExecution
import IntegerMultBounds.Machine.PrefixCounter

/-! Actual shared-control scheduling after multi-control translation. Only the
common physical control bank advances; the old leaf copies and binary output
remain stale until the next verified recurring evaluator refreshes them. -/
namespace IntegerMultBounds.Machine.MultiControlPrefixTranslationExecution

open RadixLinearCombinationRefresh (Expr controls leaves)
open MultiControlTranslationExecution (TapeCount)
variable {c radix : ℕ}

abbrev read (seed : Fin c) (xs : Fin c → List (Fin radix)) := RadixLinearCombinationShared.read seed xs

/-- Current physical controls and the actual previous arithmetic state. -/
def bank (e : Expr c) (seed : Fin c) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied : List Bool)
    (xs old : Fin c → List (Fin radix)) : Tapes (TapeCount e) radix :=
  MultiControlTranslationExecution.bank e source dest p q bs qs supplied (read seed xs) (read seed old)

private theorem controls_eq (seed : Fin c) (xs : Fin c → List (Fin radix)) :
    controls (read seed xs) = PrefixCounter.tapes (fun _ => MarkedWordCleanup.empty) xs := by
  unfold controls PrefixCounter.tapes
  congr 1
  funext i
  simp only [RadixLinearCombinationShared.read_at]
  rfl

variable [Fact radix.Prime]

def advance (order : List (Fin c)) (xs : Fin c → List (Fin radix)) :=
  PrefixCounterData.advanceFields (Fact.out : radix.Prime).two_le order xs

/-- Controls are already a literal first bank; every other tape is a frame. -/
def prefixProgram (e : Expr c) (order : List (Fin c)) (hne : order ≠ []) :
    Program (TapeCount e) (c*3+1) radix :=
  extend (extend (PrefixCounter.program (Fact.out : radix.Prime).two_le order hne)
    (RadixLinearCombinationBinary.TapeCount e.erase)) 12

theorem prefix_hoare (e : Expr c) (seed : Fin c) (order : List (Fin c)) (hne : order ≠ []) (hnodup : order.Nodup)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied : List Bool) (xs old : Fin c → List (Fin radix)) :
    HoareTime (prefixProgram e order hne) (fun v => v = bank e seed source dest p q bs qs supplied xs old)
      (fun v => v = bank e seed source dest p q bs qs supplied (advance order xs) old)
      (PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order xs) := by
  have hh := PrefixCounter.increment_hoare (Fact.out : radix.Prime).two_le order hne hnodup
    (fun _ => MarkedWordCleanup.empty) xs (by intro i; rfl)
    (by intro i; simp [MarkedWordCleanup.empty,show (1:ℤ)+(xs i).length ≠ 0 by omega])
  rw [← controls_eq seed xs,← controls_eq seed (PrefixCounterData.advanceFields (Fact.out : radix.Prime).two_le order xs)] at hh
  exact FamilyPlacementAlphabet.extend_hoare
    (FamilyPlacementAlphabet.extend_hoare hh (RadixLinearCombinationBinary.bank e.erase (read seed old)
      ((RadixToBinary.binaryState radix supplied).tape 0) 1 []))
    (MultiControlTranslationExecution.translationBank source dest p q bs qs)

abbrev States (e : Expr c) := MultiControlTranslationExecution.States e+(c*3+1)

def program (e : Expr c) (order : List (Fin c)) (hne : order ≠ []) : Program (TapeCount e) (States e) radix :=
  seq (MultiControlTranslationExecution.program e) (prefixProgram e order hne)

def input (e : Expr c) (seed : Fin c) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs old : Fin c → List (Fin radix)) : Tapes (TapeCount e) radix :=
  bank e seed (putWord source p blocks.flatten) dest p q bs qs
    (MultiControlTranslationExecution.bits e (read seed old)) xs old

def output (e : Expr c) (seed : Fin c) (order : List (Fin c)) (b B : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs : Fin c → List (Fin radix)) : Tapes (TapeCount e) radix :=
  bank e seed (putWord source p blocks.flatten)
    (putWord dest q (BlockRotationData.rotate (MultiControlTranslationExecution.offset e (read seed xs)) blocks).flatten)
    (p+radix^b*B) (q+radix^b*B) bs qs (MultiControlTranslationExecution.bits e (read seed xs))
    (advance order xs) xs

/-- Complete recurring fiber and real carry advancement, with the exact carry
charge left visible for stream amortization. No per-fiber tape data is supplied. -/
theorem translate_hoare (e : Expr c) (seed : Fin c) (order : List (Fin c)) (hne : order ≠ []) (hnodup : order.Nodup)
    (b B : ℕ) (hB : 0 < B) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs old : Fin c → List (Fin radix))
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i, (old i).length = b)
    (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (program e order hne) (fun v => v = input e seed source dest p q blocks bs qs xs old)
      (fun v => v = output e seed order b B source dest p q blocks bs qs xs)
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+496)*(radix^b*B)+1+
        PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order xs) := by
  have ht := MultiControlTranslationExecution.translate_finite_after_advance e seed b B hB source dest p q blocks
    bs qs xs old hw ho hlen hwidth hb hq cb cq
  exact ht.seq (prefix_hoare e seed order hne hnodup (putWord source p blocks.flatten)
    (putWord dest q (BlockRotationData.rotate (MultiControlTranslationExecution.offset e (read seed xs)) blocks).flatten)
    (p+radix^b*B) (q+radix^b*B) bs qs (MultiControlTranslationExecution.bits e (read seed xs)) xs xs)

end IntegerMultBounds.Machine.MultiControlPrefixTranslationExecution
