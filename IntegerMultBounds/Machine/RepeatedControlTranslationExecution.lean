import IntegerMultBounds.Machine.FixedControlTranslationStream
import IntegerMultBounds.Machine.ExactFrame

/-! One heterogeneous H group: execute every middle-spectator D fiber with
fixed H, then physically increment H once. All loop controls are restored. -/
namespace IntegerMultBounds.Machine.RepeatedControlTranslationExecution
variable {radix : ℕ} [Fact radix.Prime]
open TranslationStream (fibers)

private def incrementPlacement : Fin (1+15) ≃ Fin 16 := Equiv.swap 0 15

def incrementProgram : Program 16 3 radix :=
  Placement.placed (RadixCounter.program (Fact.out : radix.Prime).two_le) incrementPlacement

theorem increment_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs supplied old : List Bool) (xs : List (Fin radix)) :
    HoareTime incrementProgram
      (fun v => v = RationalTranslationExecution.bank source dest p q bs qs supplied old xs)
      (fun v => v = RationalTranslationExecution.bank source dest p q bs qs supplied old
        (RadixCounterData.increment (Fact.out : radix.Prime).two_le xs))
      (2*RadixCounterData.carrySteps xs) := by
  have hc := RadixCounter.increment_hoare (Fact.out : radix.Prime).two_le MarkedWordCleanup.empty xs rfl
    (by simp [MarkedWordCleanup.empty,show (1:ℤ)+xs.length ≠ 0 by omega])
  have ha : Placement.active incrementPlacement (RationalTranslationExecution.bank source dest p q bs qs supplied old xs) =
      RadixCounter.tapes MarkedWordCleanup.empty xs := by
    unfold Placement.active incrementPlacement RationalTranslationExecution.bank Tapes.append
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active incrementPlacement
      (RationalTranslationExecution.bank source dest p q bs qs supplied old (RadixCounterData.increment (Fact.out : radix.Prime).two_le xs)) =
      RadixCounter.tapes MarkedWordCleanup.empty (RadixCounterData.increment (Fact.out : radix.Prime).two_le xs) := by
    unfold Placement.active incrementPlacement RationalTranslationExecution.bank Tapes.append
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra incrementPlacement (RationalTranslationExecution.bank source dest p q bs qs supplied old xs) =
      Placement.extra incrementPlacement
        (RationalTranslationExecution.bank source dest p q bs qs supplied old (RadixCounterData.increment (Fact.out : radix.Prime).two_le xs)) := by
    unfold Placement.extra incrementPlacement RationalTranslationExecution.bank Tapes.append
    congr 1
    funext i
    fin_cases i <;> rfl
  apply (Placement.hoare_at hc incrementPlacement _ ha).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _


def bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs old : List Bool) (xs : List (Fin radix)) :=
  CountedLoopReuseAlphabet.bank (RationalTranslationExecution.bank source dest p q bs qs old old xs)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary cs) 1 1

def program (r : ℚ) :=
  seq (FixedControlTranslationStream.program (radix := radix) r) (extend (incrementProgram (radix := radix)) 2)

theorem group_hoare (r : ℚ) {B C : ℕ} (hB : 0 < B) (hC : 0 < C)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs old : List Bool) (xs : List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length) (hc : Counter.value cs = C)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cold : GrowingCounterData.Canonical old)
    (hold : Counter.value old < radix^xs.length) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (program r)
      (fun v => v = bank (putWord source p (fibers (radix^xs.length) C payload).flatten)
        dest p q bs qs cs old xs)
      (fun v => v = bank (putWord source p (fibers (radix^xs.length) C payload).flatten)
        (putWord dest q (FixedControlTranslationStream.outputPrefix r xs C payload))
        (p+((C*(radix^xs.length*B) : ℕ) : ℤ)) (q+((C*(radix^xs.length*B) : ℕ) : ℤ))
        bs qs cs (RationalOffsetPrepare.result r xs) (RadixCounterData.increment (Fact.out : radix.Prime).two_le xs))
      (557*(C*(radix^xs.length*B))) := by
  have ht := FixedControlTranslationStream.translate_hoare_linear r hB source dest p q bs qs cs old xs
    hb hq hc cb cq cc cold hold payload hwidth
  rw [TranslationStream.source_length _ B C _ hwidth] at ht
  obtain ⟨c,hce⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hC)
  have hd : FixedControlTranslationStream.descriptor r old xs C = RationalOffsetPrepare.result r xs := by
    rw [hce]; rfl
  have hn := hoare_extend_eq (increment_hoare
    (putWord source p (fibers (radix^xs.length) C payload).flatten)
    (putWord dest q (FixedControlTranslationStream.outputPrefix r xs C payload))
    (p+((C*(radix^xs.length*B) : ℕ) : ℤ)) (q+((C*(radix^xs.length*B) : ℕ) : ℤ))
    bs qs (RationalOffsetPrepare.result r xs) (RationalOffsetPrepare.result r xs) xs)
    (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary cs) 1 1)
  have ht' : HoareTime (FixedControlTranslationStream.program r)
      (fun v => v = bank (putWord source p (fibers (radix^xs.length) C payload).flatten) dest p q bs qs cs old xs)
      (fun v => v = bank (putWord source p (fibers (radix^xs.length) C payload).flatten)
        (putWord dest q (FixedControlTranslationStream.outputPrefix r xs C payload))
        (p+((C*(radix^xs.length*B) : ℕ) : ℤ)) (q+((C*(radix^xs.length*B) : ℕ) : ℤ))
        bs qs cs (RationalOffsetPrepare.result r xs) xs) (529*(C*(radix^xs.length*B))+23) := by
    simp only [FixedControlTranslationStream.state,hd] at ht
    simpa only [bank,FixedControlTranslationStream.outputPrefix,
      TranslationPreparedFamily.outputPrefix,List.range_zero,List.map_nil,List.flatten_nil,
      FixedControlTranslationStream.descriptor,hd,zero_mul,Nat.cast_zero,add_zero,putWord] using ht
  apply (ht'.seq hn).consequence (fun _ h => h) (fun _ h => h) ?_
  have hcarr := (RadixCounterData.carrySteps_bounds xs).2
  have hw := RadixToBinaryData.width_le_power (Fact.out : radix.Prime).two_le xs.length
  have hQ : 0 < radix^xs.length := pow_pos (Fact.out : radix.Prime).pos _
  have hv : radix^xs.length ≤ C*(radix^xs.length*B) :=
    (Nat.le_mul_of_pos_right _ hB).trans (Nat.le_mul_of_pos_left _ hC)
  nlinarith

end IntegerMultBounds.Machine.RepeatedControlTranslationExecution
