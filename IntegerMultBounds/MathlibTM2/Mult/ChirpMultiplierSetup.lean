module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpMultiplierDimensions

/-! # Install actual multiplier readiness counters from binary q and w -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.Schoenhage.Schedule

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U} {rg : TblR 5 → Fin T}

def chirpMultiplierAssignments (cr : CR → Fin T) : List (Fin 5 × Fin T) :=
  [(1, cr .wn), (0, cr .pn), (3, cr .nn)]

def chirpMultiplierSetup (rg : TblR 5 → Fin T) (cr : CR → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg tblChirpMultiplierDimensions)
    (.seq (tblUnaryCopies rg (chirpMultiplierAssignments cr)) (tblCompile rg tblChirpMultiplierDimensionsClear))

def chirpMultiplierSetupCost (W e q w : ℕ) : ℕ :=
  (4 * Nat.size (2 * w) + 10) * tblC W e +
    6 * (w + q + topN w) + 33 * W + 19

/-- Generate all three unary counters, including topN, and restore the entire binary bank. -/
theorem chirpMultiplierSetup_exec (hrg : Function.Injective rg) (cr : CR → Fin T)
    (hout : ∀ r ∈ [CR.wn, .pn, .nn], ∀ i, rg i ≠ cr r)
    {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 5 A) (q w : ℕ) (hq : st.val 0 = q) (hw : st.val 1 = w) (hw1 : 1 ≤ w)
    (hroom : 4 * w + 2 < 2 ^ W)
    (hzero : ∀ i : Fin 5, 2 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpMultiplierSetupCost W e q w ∧
      Exec body (chirpMultiplierSetup rg cr) (mk v S) n
        (mk v' { S with R := unaryCopiesR (chirpMultiplierDimensionValues q w) S.R (chirpMultiplierAssignments cr) }) := by
  have hcopies : unaryCopiesCost W (chirpMultiplierDimensionValues q w) (chirpMultiplierAssignments cr) =
      6 * (w + q + topN w) + 33 * W + 19 := by
    simp [unaryCopiesCost, chirpMultiplierAssignments, chirpMultiplierDimensionValues]
    ring
  obtain ⟨v', n, hu, hn, he⟩ := tblComputedUnaryCopies_exec (body := body) hrg wl nl hwl hnl heW
    tblChirpMultiplierDimensions tblChirpMultiplierDimensionsClear st (chirpMultiplierDimensionValues q w)
    (4 * Nat.size (2 * w) + 7) 3
    (tblChirpMultiplierDimensions_do st q w hq hw hw1 hroom hfit)
    (fun z hz => tblChirpMultiplierDimensionsClear_do st z (by
      intro i hi
      rw [hz]
      fin_cases i <;> first | (simp at hi; done) | simp [chirpMultiplierDimensionValues, hq, hw]) hzero)
    hfit (chirpMultiplierAssignments cr) (by
      intro a ha
      simp only [chirpMultiplierAssignments, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      all_goals exact hout _ (by simp)) v S hS
  refine ⟨v', n, hu, ?_, he⟩
  simpa only [hcopies, chirpMultiplierSetupCost, Nat.add_assoc] using hn

/-- From a fresh data bank, the installed counters prove the multiplier's full Ready contract. -/
theorem chirpMultiplierSetup_ready (cr : CR → Fin T) (hcr : Function.Injective cr)
    (R : Regs T A) (q w : ℕ) (hblank : ∀ r, r ≠ .xs → R (cr r) = []) :
    Ready (fun r => unaryCopiesR (chirpMultiplierDimensionValues q w) R (chirpMultiplierAssignments cr) (cr r)) w q := by
  constructor <;> simp [unaryCopiesR, chirpMultiplierAssignments, chirpMultiplierDimensionValues,
    hcr.eq_iff, hblank]

/-- Only the three readiness counters change, so arbitrary source words and spectators are kept. -/
theorem chirpMultiplierSetup_off (cr : CR → Fin T) (R : Regs T A) (q w : ℕ) (k : Fin T)
    (hw : k ≠ cr .wn) (hp : k ≠ cr .pn) (hn : k ≠ cr .nn) :
    unaryCopiesR (chirpMultiplierDimensionValues q w) R (chirpMultiplierAssignments cr) k = R k := by
  apply unaryCopiesR_off
  intro a ha
  simp only [chirpMultiplierAssignments, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact hw.symm
  · exact hp.symm
  · exact hn.symm

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
