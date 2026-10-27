module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoefficientSweep

/-! Binary offset sweeps reuse prepared constants throughout the coefficient sequence. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling.WeightNat IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

structure CoefficientSweepReady {A : ℕ} (P q s t u band i : ℕ) (st : TblSt 50 A) : Prop where
  sourceSample : st.val 26 = similarityGridNumerator P s t u (liftedSource s band i)
  pi : st.val 18 = piN P
  precision : st.val 19 = P
  sign : st.val 22 = 1
  dimension : st.val 34 = s
  period : st.val 35 = t
  parameter : st.val 36 = u
  source : st.val 37 = liftedSource s band i
  grid : st.val 39 = 2^q
  scale : st.val 40 = 2^P
  bandwidth : st.val 49 = band

theorem CoefficientSweepReady.of_frame {A P q s t u band i : ℕ} {st st' : TblSt 50 A}
    (h : CoefficientSweepReady P q s t u band i st)
    (hf : ∀ r ∈ [(26 : Fin 50),18,19,22,34,35,36,37,39,40,49], st'.val r = st.val r) :
    CoefficientSweepReady P q s t u band i st' := by
  exact ⟨(hf 26 (by simp)).trans h.sourceSample,(hf 18 (by simp)).trans h.pi,(hf 19 (by simp)).trans h.precision,
    (hf 22 (by simp)).trans h.sign,(hf 34 (by simp)).trans h.dimension,
    (hf 35 (by simp)).trans h.period,(hf 36 (by simp)).trans h.parameter,
    (hf 37 (by simp)).trans h.source,(hf 39 (by simp)).trans h.grid,
    (hf 40 (by simp)).trans h.scale,(hf 49 (by simp)).trans h.bandwidth⟩

def coefficientSweepWords (negative : Bool) (P q s t u band i count : ℕ) : List GaussianInt :=
  (List.range count).map (fun n => signedCoefficientWord negative P q s t u band i
    (if negative then band-n else n+1))

def preparedCoefficientSweep (negative : Bool) : TblCode 50 :=
  tblFor 48 49 (coefficientSweepStep negative)

theorem preparedCoefficientSweep_do {A w q P s t u band i : ℕ}
    (negative : Bool) (st : TblSt 50 A) (hready : CoefficientSweepReady P q s t u band i st)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s) :
    TblDo A (liftedCoefficientWidth P q w s t u band) w (preparedCoefficientSweep negative) st
      (fun st' => CoefficientSweepReady P q s t u band i st' ∧
        st'.acc = (cstream A w (coefficientSweepWords negative P q s t u band i band)).reverse++st.acc)
      (band*(620*P+256)+3) := by
  let V := liftedCoefficientWidth P q w s t u band
  let F := fun n => csyms A w (signedCoefficientWord negative P q s t u band i
    (if negative then band-n else n+1))
  let Inv := fun j (st' : TblSt 50 A) =>
    CoefficientSweepReady P q s t u band i st' ∧
    st'.acc = ((List.range j).flatMap F).reverse++st.acc
  have hbV : band < 2^V := by
    have hc := (liftedCoefficientWidth_fits negative P q w s t u band i band hi le_rfl).coordinates
    change i+band*s+band < 2^V at hc
    omega
  have hc : TblDo A V w (preparedCoefficientSweep negative) st
      (fun st' => CoefficientSweepReady P q s t u band i st' ∧
        st'.acc = ((List.range band).flatMap F).reverse++st.acc)
      (1+(band*((620*P+253)+1+2)+2)) := by
    apply TblDo.for band (620*P+253) hready.bandwidth hbV (by decide) Inv
    · constructor
      · apply hready.of_frame
        intro r hr
        have hn : r ≠ (48 : Fin 50) := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        simp [hn]
      · simp
    · intro n hn st₁ ⟨hready₁,hacc⟩ hindex hcount
      have hrow := coefficientSweepStep_do (A := A) (w := w) negative st₁ hready₁.sourceSample hready₁.pi
        hready₁.precision hready₁.sign hready₁.dimension hready₁.period hready₁.parameter
        hready₁.source hindex hready₁.bandwidth hready₁.grid hready₁.scale hs0 hst hP hn hi
      refine hrow.mono (fun st₂ h => ⟨h.2.2.2.2.2.1.trans hindex,
        h.2.2.2.2.2.2.1.trans hcount,?_,?_⟩) le_rfl
      · apply hready₁.of_frame
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact h.2.2.2.2.2.2.2
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2.1
        · exact h.2.2.2.2.1 34 (by decide) (by decide) (by decide)
        · exact h.2.2.2.2.1 35 (by decide) (by decide) (by decide)
        · exact h.2.2.2.2.1 36 (by decide) (by decide) (by decide)
        · exact h.2.2.2.2.1 37 (by decide) (by decide) (by decide)
        · exact h.2.2.2.2.1 39 (by decide) (by decide) (by decide)
        · exact h.2.2.2.2.1 40 (by decide) (by decide) (by decide)
        · exact h.2.2.2.2.2.2.1
      · rw [h.1,hacc,List.range_succ]
        simp [F,List.reverse_append,List.append_assoc]
    · intro st' hI _ _
      exact hI
  refine hc.mono (fun st' h => ?_) (by nlinarith)
  simpa [coefficientSweepWords,cstream,List.flatMap_map,F,Function.comp_def] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
