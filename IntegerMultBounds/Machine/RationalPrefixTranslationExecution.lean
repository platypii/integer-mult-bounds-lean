import IntegerMultBounds.Machine.RationalTranslationExecution
import IntegerMultBounds.Machine.PrefixCounter

/-! Concrete translation with a mixed-prefix scheduler. Physical field zero
supplies the rational control value; the fixed carry order may place it anywhere.
The remaining fields are genuine spectator tapes with arbitrary independent
widths. Translation preserves them exactly; the scheduler visits only carries. -/
namespace IntegerMultBounds.Machine.RationalPrefixTranslationExecution

variable {radix c : ℕ}

/-- Every additional prefix field has its own retained sentinel and head at one. -/
def extra (fields : Fin (c+1) → List (Fin radix)) : Tapes c radix :=
  ⟨fun _ => 1,fun i => RadixRationalBinary.source (fields i.succ)⟩

/-- Selected field zero is tape15; the other fields follow the sixteen-tape body. -/
def bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied old : List Bool)
    (fields : Fin (c+1) → List (Fin radix)) : Tapes (16+c) radix :=
  (RationalTranslationExecution.bank source dest p q bs qs supplied old (fields 0)).append (extra fields)

/-- Prefix fields form a contiguous physical suffix; the first fifteen tapes are frames. -/
def prefixPlacement (c : ℕ) : Fin ((c+1)+15) ≃ Fin (16+c) :=
  (finAddFlip : Fin ((c+1)+15) ≃ Fin (15+(c+1))).trans (finCongr (by omega))

private theorem placed_zero : prefixPlacement c (Fin.castAdd 15 (0 : Fin (c+1))) = Fin.castAdd c (15 : Fin 16) := by
  apply Fin.ext
  simp [prefixPlacement,finAddFlip_apply_castAdd]

private theorem placed_succ (i : Fin c) : prefixPlacement c (Fin.castAdd 15 i.succ) = Fin.natAdd 16 i := by
  apply Fin.ext
  simp [prefixPlacement,finAddFlip_apply_castAdd]
  omega

private theorem placed_extra (i : Fin 15) :
    prefixPlacement c (Fin.natAdd (c+1) i) = Fin.castAdd c (Fin.castAdd 1 i) := by
  apply Fin.ext
  simp [prefixPlacement,finAddFlip_apply_natAdd]

private theorem active_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied old : List Bool)
    (fields : Fin (c+1) → List (Fin radix)) :
    Placement.active (prefixPlacement c) (bank source dest p q bs qs supplied old fields) =
      PrefixCounter.tapes (fun _ => MarkedWordCleanup.empty) fields := by
  unfold Placement.active
  congr 1
  · funext i
    induction i using Fin.cases with
    | zero => rw [placed_zero]; rfl
    | succ i =>
      rw [placed_succ]
      simp only [bank,Tapes.append,Fin.addCases_right,extra]
  · funext i
    induction i using Fin.cases with
    | zero => rw [placed_zero]; rfl
    | succ i =>
      rw [placed_succ]
      simp only [bank,Tapes.append,Fin.addCases_right,extra]
      rfl

private theorem extra_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied old : List Bool)
    (fields next : Fin (c+1) → List (Fin radix)) :
    Placement.extra (prefixPlacement c) (bank source dest p q bs qs supplied old fields) =
      Placement.extra (prefixPlacement c) (bank source dest p q bs qs supplied old next) := by
  unfold Placement.extra
  congr 1
  funext i
  rw [placed_extra]
  fin_cases i <;> rfl

variable [Fact radix.Prime]

def prefixProgram (order : List (Fin (c+1))) (hne : order ≠ []) : Program (16+c) ((c+1)*3+1) radix :=
  Placement.placed (PrefixCounter.program (Fact.out : radix.Prime).two_le order hne) (prefixPlacement c)

/-- Exact complete bank update by the finite carry scheduler. -/
theorem prefix_hoare (order : List (Fin (c+1))) (hne : order ≠ []) (hnodup : order.Nodup)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied old : List Bool)
    (fields : Fin (c+1) → List (Fin radix)) :
    HoareTime (prefixProgram order hne)
      (fun v => v = bank source dest p q bs qs supplied old fields)
      (fun v => v = bank source dest p q bs qs supplied old
        (PrefixCounterData.advanceFields (Fact.out : radix.Prime).two_le order fields))
      (PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order fields) := by
  have hh := PrefixCounter.increment_hoare (Fact.out : radix.Prime).two_le order hne hnodup
    (fun _ => MarkedWordCleanup.empty) fields (by intro i; rfl)
    (by intro i; simp [MarkedWordCleanup.empty,show (1:ℤ)+(fields i).length ≠ 0 by omega])
  have hp := Placement.hoare_at hh (prefixPlacement c) (bank source dest p q bs qs supplied old fields)
    (active_bank source dest p q bs qs supplied old fields)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,extra_bank,← active_bank]
  exact Placement.view _ _

/-- Concrete rational translation then actual mixed-prefix advancement. -/
def program (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) :
    Program (16+c) ((((4+((2+(2*r.num.natAbs+r.den+1)+2)+18+6))+7)+217)+((c+1)*3+1)) radix :=
  seq (extend (RationalTranslationExecution.program r) c) (prefixProgram order hne)

def input (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs supplied old : List Bool) (fields : Fin (c+1) → List (Fin radix)) : Tapes (16+c) radix :=
  bank (putWord source p blocks.flatten) dest p q bs qs supplied old fields

def output (r : ℚ) (order : List (Fin (c+1))) (B : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (fields : Fin (c+1) → List (Fin radix)) : Tapes (16+c) radix :=
  bank (putWord source p blocks.flatten)
    (putWord dest q (BlockRotationData.rotate (Counter.value (RationalOffsetPrepare.result r (fields 0))) blocks).flatten)
    (p+radix^(fields 0).length*B) (q+radix^(fields 0).length*B) bs qs
    (RationalOffsetPrepare.result r (fields 0)) (RationalOffsetPrepare.result r (fields 0))
    (PrefixCounterData.advanceFields (Fact.out : radix.Prime).two_le order fields)

/-- Only carry propagation is charged for spectators; their widths are not scanned
on every fiber. The cost retains the exact scheduler charge for amortization. -/
theorem translate_hoare (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) (hnodup : order.Nodup)
    (B : ℕ) (hB : 0 < B) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs supplied old : List Bool) (fields : Fin (c+1) → List (Fin radix))
    (hlen : blocks.length = radix^(fields 0).length) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(fields 0).length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cs : GrowingCounterData.Canonical supplied) (co : GrowingCounterData.Canonical old)
    (hs : Counter.value supplied < radix^(fields 0).length) (ho : Counter.value old < radix^(fields 0).length) :
    HoareTime (program r order hne)
      (fun v => v = input source dest p q blocks bs qs supplied old fields)
      (fun v => v = output r order B source dest p q blocks bs qs fields)
      (516*(radix^(fields 0).length*B)+1+PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order fields) := by
  have ht := (RationalTranslationExecution.translate_hoare_fiber r B hB source dest p q blocks
    bs qs supplied old (fields 0) hlen hwidth hb hq cb cq cs co hs ho).extend (extra fields)
  have ht' : HoareTime (extend (RationalTranslationExecution.program r) c)
      (fun v => v = input source dest p q blocks bs qs supplied old fields)
      (fun v => v = bank (putWord source p blocks.flatten)
        (putWord dest q (BlockRotationData.rotate (Counter.value (RationalOffsetPrepare.result r (fields 0))) blocks).flatten)
        (p+radix^(fields 0).length*B) (q+radix^(fields 0).length*B) bs qs
        (RationalOffsetPrepare.result r (fields 0)) (RationalOffsetPrepare.result r (fields 0)) fields)
      (516*(radix^(fields 0).length*B)) := by
    apply ht.consequence _ _ le_rfl
    · intro v hv; exact ⟨_,rfl,hv⟩
    · rintro v ⟨w,rfl,hv⟩; exact hv
  exact ht'.seq (prefix_hoare order hne hnodup (putWord source p blocks.flatten)
    (putWord dest q (BlockRotationData.rotate (Counter.value (RationalOffsetPrepare.result r (fields 0))) blocks).flatten)
    (p+radix^(fields 0).length*B) (q+radix^(fields 0).length*B) bs qs
    (RationalOffsetPrepare.result r (fields 0)) (RationalOffsetPrepare.result r (fields 0)) fields)

end IntegerMultBounds.Machine.RationalPrefixTranslationExecution
