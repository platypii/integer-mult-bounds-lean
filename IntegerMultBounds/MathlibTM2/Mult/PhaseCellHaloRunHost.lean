module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupHost
public import IntegerMultBounds.MathlibTM2.Fast.TableMappedHost

/-! Execute the per-phase run producer and project its emissions to binary symbols. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def haloRunHost (flags : Bool) (out : Fin 117) : Pr P 117 Q A U :=
  tblMapHost originReg (haloRunCode flags) out (fun sym => bitSymbol (a := A) (pairRe sym))

theorem runPairStream_length (flags : Bool) (A w : ℕ) (xs : List (Bool × ℕ)) :
    (runPairStream flags A w xs).length = xs.length*w := by
  simp [runPairStream,List.length_flatMap,tblPairs]

theorem runPairStream_counts_real_bits {A W : ℕ} (hA : 4 ≤ A) (xs : List (Bool × ℕ))
    (hfit : ∀ r ∈ xs, r.2 < 2^W) :
    (runPairStream false A W xs).map (fun sym => bitSymbol (a := A) (pairRe sym)) =
      xs.flatMap (fun r => binSyms W r.2) := by
  rw [runPairStream,List.map_flatMap]
  apply List.flatMap_congr
  intro r hr
  exact tblPairs_real_bits hA (hfit r hr)

theorem runPairStream_flags_real_bits {A : ℕ} (hA : 4 ≤ A) (xs : List (Bool × ℕ)) :
    (runPairStream true A 1 xs).map (fun sym => bitSymbol (a := A) (pairRe sym)) =
      xs.map (fun r => bitSymbol (a := A) r.1) := by
  have hword (flag : Bool) :
      (tblPairs A 1 (if flag then 1 else 0) 0).map (fun sym => bitSymbol (a := A) (pairRe sym)) =
        [bitSymbol (a := A) flag] := by
    rw [tblPairs_real_bits hA (by cases flag <;> decide)]
    cases flag <;> simp [binSyms,List.ofFn_succ]
  simp only [runPairStream,↓reduceIte,List.map_flatMap]
  simp only [hword]
  exact List.map_eq_flatMap.symm

theorem haloRunHost_exec {W w s t band a b : ℕ} (flags : Bool) (out : Fin 117)
    (hout : ∀ r, originReg r ≠ out) (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hc : st.val 3 = 0)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hcount : st.val 15 = t-s+1) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) (hw : w ≤ W)
    (hbound : ∀ r, st.val r < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate w tick) st)) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (40*(t-s+1)+6)*tblC W w+
        2*((2*(haloRunIntervals s t band a b).length+1)*w)+2 ∧
      Exec body (haloRunHost flags out) (mk v S) m (mk v' S') ∧
      S'.R out = ((runPairStream flags A w
        (IntervalRunMask.runs 0 s (haloRunIntervals s t band a b))).map
          (fun sym => bitSymbol (a := A) (pairRe sym)))++S.R out ∧
      tblHolds originReg S' (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨st'.val,[]⟩) ∧
      (∀ r, st'.val r < 2^W) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hcode := haloRunCode_do (A := A) (W := W) (w := w) flags st hs' hband hc hden hone hz
    hcount ha hb has hbs hs hst hwide
  obtain ⟨v',S',m,st',⟨hpost,hbounded⟩,hu,hm,he,ho,hh,hi,ho',hl,hf⟩ :=
    tblMapHost_runs (body := body) (fun sym => bitSymbol (a := A) (pairRe sym)) originReg_injective hout
      (List.replicate W tick) (List.replicate w tick) (by simp) (by simp) hw
      (hcode.bounded hbound) hbound v S hS
  refine ⟨v',S',m,st',hu,?_,he,?_,hh,hbounded,hi,ho',hl,hf⟩
  · simpa [hpost,hacc,runPairStream_length,IntervalRunMask.length_runs] using hm
  · simpa [hpost,hacc,List.map_reverse] using ho

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
