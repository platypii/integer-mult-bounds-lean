module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientBody

/-! # Generate the complete off-diagonal distance vector

Pi is generated once; one corrected exponential is evaluated per distance.
The square factor page can then reuse prefixes of this vector.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

def coefficientStreamCode : TblCode 48 :=
  tblPiSetup48 ;;
    tblBlock 48 [.copy 34 21, .zero 22, .inc 22, .zero 39, .inc 39, .zero 41] (.mul 36 35 40) ;;
      tblFor 37 42 coefficientBody

/-- A single conservative arithmetic width pays for every distance. -/
theorem coefficientWidth_facts {P s t u L V : ℕ} (hP : 13 ≤ P) (hs : 0 < s)
    (hst : s ≤ t) (hu : 1 ≤ u)
    (hV : u * t * (L + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V) :
    13 * P + 8 ≤ V ∧ u * t < 2 ^ V ∧ L < 2 ^ V ∧
      ∀ k < L, k * k < 2 ^ V ∧ u * t * k ^ 2 * 2 ^ (5 * P + 2) < 2 ^ V := by
  have hb : 1 ≤ u * t := by nlinarith
  have hsq : 1 ≤ (L + 1) ^ 2 := one_le_pow₀ (by omega)
  have hp : 1 ≤ 2 ^ (13 * P + 8) := Nat.one_le_two_pow
  have hbase : 1 ≤ u * t * (L + 1) ^ 2 := by nlinarith
  have hpow : 2 ^ (13 * P + 8) < 2 ^ V := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hbase) hV
  have hword : 13 * P + 8 < V := (Nat.pow_lt_pow_iff_right (by decide)).mp hpow
  have hsize : u * t * (L + 1) ^ 2 < 2 ^ V := by nlinarith
  have hL : L < 2 ^ V := by nlinarith [sq_nonneg (L : ℤ)]
  refine ⟨by omega, by nlinarith, hL, ?_⟩
  intro k hk
  have hk2 : k ^ 2 ≤ (L + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hlow : 2 ^ (5 * P + 2) ≤ 2 ^ (13 * P + 8) := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨?_, (Nat.mul_le_mul (Nat.mul_le_mul_left (u * t) hk2) hlow).trans_lt hV⟩
  rw [← pow_two]
  nlinarith only [hk2, hb, hsize]

/-- Numerical headers generate the exact integer distance-vector model. -/
theorem coefficientStreamCode_do {A V w P s t u band L : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hs' : st.val 34 = s) (ht' : st.val 35 = t)
    (hu' : st.val 36 = u) (hb' : st.val 38 = band) (hL' : st.val 42 = L)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hV : u * t * (L + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V) :
    TblDo A V w coefficientStreamCode st (fun st' =>
      st'.acc = (cstream A w (distanceFactorWords P s t u band L)).reverse ++ st.acc)
      (L * (310 * P + 114) + (160 * P + 450)) := by
  obtain ⟨hword, hbaseV, hLV, hterms⟩ := coefficientWidth_facts hP hs hst hu hV
  have hpi := tbl_pi48_do (W := V) (w := w) st hP' (by omega) (by omega)
  refine (hpi.seq (K₂ := 7 + (1 + (L * ((310 * P + 111) + 1 + 2) + 2)))
    (fun s₁ ⟨h18, hacc, hframe⟩ => ?_)).mono (fun _ h => h) (by ring_nf; omega)
  refine (TblDo.block (A := A) (W := V) (w := w) _ _ ?_ rfl).seq (fun s₂ he => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hframe (36 : Fin 48) (by decide),
      hframe (35 : Fin 48) (by decide), hu', ht', hbaseV]
    omega
  subst s₂
  let s₂ := tblExactList A w ([.copy 34 21, .zero 22, .inc 22, .zero 39, .inc 39, .zero 41] ++
    [.mul 36 35 40]) s₁
  have hv : s₂.val 18 = piN P ∧ s₂.val 19 = P ∧ s₂.val 21 = s ∧ s₂.val 22 = 1 ∧
      s₂.val 38 = band ∧ s₂.val 39 = 1 ∧ s₂.val 40 = u * t ∧ s₂.val 41 = 0 ∧
      s₂.val 42 = L ∧ s₂.acc = st.acc := by
    simp [s₂, tblExactList, TblIns.exact, h18, hacc,
      hframe (19 : Fin 48) (by decide), hframe (34 : Fin 48) (by decide),
      hframe (35 : Fin 48) (by decide), hframe (36 : Fin 48) (by decide),
      hframe (38 : Fin 48) (by decide), hframe (42 : Fin 48) (by decide),
      hP', hs', ht', hu', hb', hL']
  obtain ⟨g18, g19, g21, g22, gb, g1, gbase, gz, gL, gacc⟩ := hv
  let F := fun k : ℕ => csyms A w (distanceFactorWord P s t u band k)
  let Inv := fun j (s' : TblSt 48 A) =>
    s'.acc = ((List.range j).flatMap F).reverse ++ st.acc ∧
    s'.val 18 = piN P ∧ s'.val 19 = P ∧ s'.val 21 = s ∧ s'.val 22 = 1 ∧
    s'.val 38 = band ∧ s'.val 39 = 1 ∧ s'.val 40 = u * t ∧ s'.val 41 = 0
  refine TblDo.for L (310 * P + 111) gL hLV (by decide) Inv ?_ ?_ ?_
  · exact ⟨by simpa only [List.range_zero, List.flatMap_nil, List.reverse_nil, List.nil_append] using gacc,
      g18, g19, g21, g22, gb, g1, gbase, gz⟩
  · intro k hk s' ⟨ga, gp, gP, gs, gn, gw, go, gB, gZ⟩ gk gN
    refine (coefficientBody_do s' gp gP gs gn gk gw go gB gZ hP hs hword
      (hterms k hk).1 (hterms k hk).2).mono ?_ le_rfl
    intro s'' ⟨hout, hp'', hP'', hs'', hn'', hkeep⟩
    refine ⟨(hkeep 37 (by decide)).trans gk, (hkeep 42 (by decide)).trans gN, ?_⟩
    change Inv (k + 1) ⟨Function.update s''.val 37 (k + 1), s''.acc⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hout, ga, tbl_range_flatMap_succ]
      simp [F, List.reverse_append, List.append_assoc]
    · simpa using hp''.trans gp
    · simpa using hP''.trans gP
    · simpa using hs''.trans gs
    · simpa using hn''.trans gn
    · simpa using (hkeep 38 (by decide)).trans gw
    · simpa using (hkeep 39 (by decide)).trans go
    · simpa using (hkeep 40 (by decide)).trans gB
    · simpa using (hkeep 41 (by decide)).trans gZ
  · intro s' h _ _
    simpa [Inv, F, distanceFactorWords, cstream, List.flatMap_map] using h.1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
