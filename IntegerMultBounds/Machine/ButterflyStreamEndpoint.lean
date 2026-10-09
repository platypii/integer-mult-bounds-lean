import IntegerMultBounds.Machine.ButterflyStreamRun
import IntegerMultBounds.Machine.CyclicRowSplit

/-! Complete physical endpoints of the paired coefficient scan. Both produced
streams are materialized in coefficient order, original streams are preserved,
and all coefficient workspace is blank, with actual end positions specified. -/
namespace IntegerMultBounds.Machine.ButterflyStreamEndpoint
noncomputable section
open ButterflyStreamData
variable {n : ℕ}

theorem component_width (a b : Coefficient) (w : ℕ)
    (ha : a.1.length=w ∧ a.2.length=w) (hb : b.1.length=w ∧ b.2.length=w) :
    ∀ i,(componentWords a b i).length=w := by
  intro i
  rcases i with _|i
  · exact ha.1
  rcases i with _|i
  · exact ha.2
  rcases i with _|i
  · exact hb.1
  · exact hb.2

theorem result_width (a b : Coefficient) (w : ℕ)
    (ha : a.1.length=w ∧ a.2.length=w) (hb : b.1.length=w ∧ b.2.length=w) (j : Fin 2) :
    (result a b j).1.length=w ∧ (result a b j).2.length=w := by
  have hw := component_width a b w ha hb
  fin_cases j <;> constructor <;> exact ButterflyNumerator.words_length _ _ _ hw

theorem position_all (p : ℤ) (xs : Fin n → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    position p xs n=p+n*(2*(w+1)) := by
  rw [position,CyclicRowSplit.prefix_length (fun i => encoded (xs i)) (2*(w+1))
    (fun i => DelimitedRadixRecord.complex_length _ _ _ (hw i).1 (hw i).2) n le_rfl]
  push_cast
  rfl

def input (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ) (a b : Fin n → Coefficient) : Tapes 52 2 :=
  (⟨![p 0,p 1,r 0,r 1],![full (f 0) (p 0) a,full (f 1) (p 1) b,g 0,g 1]⟩ : Tapes 4 2).append
    (RadixLinearCombinationBootstrap.empty 48)

def output (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ) (a b : Fin n → Coefficient) (w : ℕ) : Tapes 52 2 :=
  (⟨![p 0+n*(2*(w+1)),p 1+n*(2*(w+1)),r 0+n*(2*(w+1)),r 1+n*(2*(w+1))],
    ![full (f 0) (p 0) a,full (f 1) (p 1) b,
      full (g 0) (r 0) (fun i => result (a i) (b i) 0),
      full (g 1) (r 1) (fun i => result (a i) (b i) 1)]⟩ : Tapes 4 2).append
    (RadixLinearCombinationBootstrap.empty 48)

theorem initial (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ) (a b : Fin n → Coefficient) :
    state f g p r a b 0=input f g p r a b := by
  simp [state,streams,position,prefixTape,CyclicRowCycle.rowPrefix,input,putWord]

theorem final (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ) (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w) :
    state f g p r a b n=output f g p r a b w := by
  simp only [state,streams,position_all _ a w ha,position_all _ b w hb,
    position_all _ (fun i => result (a i) (b i) 0) w (fun i => result_width _ _ w (ha i) (hb i) 0),
    position_all _ (fun i => result (a i) (b i) 1) w (fun i => result_width _ _ w (ha i) (hb i) 1),
    prefixTape,CyclicRowCycle.prefix_all,full,output]

/-- The full stream specification, including all count overhead, at volume-linear cost. -/
theorem runs (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ)
    (a b : Fin n → Coefficient) (w : ℕ)
    (ha : ∀ i,(a i).1.length=w ∧ (a i).2.length=w)
    (hb : ∀ i,(b i).1.length=w ∧ (b i).2.length=w)
    (bs : List Bool) (hn : 0<n) (hcount : Counter.value bs=n)
    (hcanonical : GrowingCounterData.Canonical bs) :
    HoareTime ButterflyStreamRun.program
      (fun v => v=ButterflyStreamRun.bank (input f g p r a b) bs)
      (fun v => v=ButterflyStreamRun.bank (output f g p r a b w) bs) (200*(4*n*(w+1))) := by
  have hh := ButterflyStreamRun.runs_linear f g p r a b w ha hb bs hn hcount hcanonical
  rw [initial,final f g p r a b w ha hb] at hh
  exact hh

end
end IntegerMultBounds.Machine.ButterflyStreamEndpoint
