module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinSimilaritySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSimilaritySampleAt
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDistanceSample
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinGridEmit

/-! Execute a within-cell coefficient using a retained source similarity sample. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

def withinCoefficientFromSource : TblCode 48 := withinSimilaritySetup ;;
  (.ins (.copy 26 41) ;; (similaritySampleAt true ;; (distanceSample ;; withinGridEmit)))

theorem withinCoefficientFromSource_do {A V w q P s t u band j k : ℕ} (st : TblSt 48 A)
    (hsource : st.val 26 = similarityGridNumerator P s t u j)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = j) (hk : st.val 38 = k)
    (hq : st.val 39 = 2^q) (hpowP : st.val 40 = 2^P)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P)
    (hjk : j ≠ k) (hband : ((k : ℤ)-(j : ℤ)).natAbs ≤ band)
    (hjV : 2*t*j+s < 2^V) (hkV : 2*t*k+s < 2^V)
    (hsV : 2*s < 2^V) (htV : t < 2^V)
    (hsq : s^2 < 2^V) (huV : u*s^2 < 2^V)
    (hdenV : similarityDenominator s t < 2^V)
    (hV : 13*P+8 ≤ V) (hqV : q+2*P+4 ≤ V)
    (haj : similarityNumerator s t u j*2^(5*P+2) < 2^V)
    (hak : similarityNumerator s t u k*2^(5*P+2) < 2^V)
    (hdV : naturalDistance j k^2 < 2^V)
    (htdV : t*naturalDistance j k^2 < 2^V)
    (hudV : u*(t*naturalDistance j k^2) < 2^V)
    (had : (u*t*naturalDistance j k^2)*2^(5*P+2) < 2^V) :
    TblDo A V w withinCoefficientFromSource st (fun st' =>
      st'.acc = (csyms A w (rationalWord q
        (PhaseCellConcreteCoefficients.entry P s t u band j k))).reverse ++ st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ r : Fin 48, 34 ≤ r.val → r.val ≤ 40 → st'.val r = st.val r) (620*P+238) := by
  have hjbound : j < 2^V := by
    have hh := Nat.le_mul_of_pos_left j (show 0 < 2*t by omega)
    omega
  have hkbound : k < 2^V := by
    have hh := Nat.le_mul_of_pos_left k (show 0 < 2*t by omega)
    omega
  have hajbound : similarityGridNumerator P s t u j < 2^(P+2) := by
    simpa using (similarityGridNumerator_fits (q := 0) (j := j) (u := u) hP hs0 hst le_rfl)
  have hakbound : similarityGridNumerator P s t u k < 2^(P+2) := by
    simpa using (similarityGridNumerator_fits (q := 0) (j := k) (u := u) hP hs0 hst le_rfl)
  have hdBound : distanceGridNumerator P s t u (naturalDistance j k) < 2^(P+2) :=
    (Nat.sub_le _ _).trans_lt (expPiNat_neg_lt_pow hP le_rfl _ _ hs0)
  have hprod : similarityGridNumerator P s t u j *
      distanceGridNumerator P s t u (naturalDistance j k) < 2^(2*P+4) := by
    have hh := (Nat.mul_le_mul_left (similarityGridNumerator P s t u j) hdBound.le).trans_lt
      (Nat.mul_lt_mul_of_pos_right hajbound (by positivity : 0 < 2^(P+2)))
    simpa [← pow_add,show P+2+(P+2) = 2*P+4 by omega] using hh
  have hprodV := hprod.trans_le (Nat.pow_le_pow_right (by decide) (show 2*P+4 ≤ V by omega))
  have hnumV : 2^q*(similarityGridNumerator P s t u j *
      distanceGridNumerator P s t u (naturalDistance j k)) < 2^V := by
    have hh := Nat.mul_lt_mul_of_pos_left hprod (by positivity : 0 < 2^q)
    rw [← pow_add] at hh
    exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hdivV : similarityGridNumerator P s t u k*2^P < 2^V := by
    have hh := Nat.mul_lt_mul_of_pos_right hakbound (by positivity : 0 < 2^P)
    rw [← pow_add] at hh
    exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hcore : TblDo A V w withinCoefficientFromSource st (fun st' =>
      st'.acc = (csyms A w (rationalWord q
        (PhaseCellConcreteCoefficients.entry P s t u band j k))).reverse ++ st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ r : Fin 48, 34 ≤ r.val → r.val ≤ 40 → st'.val r = st.val r)
      (5+(1+((310*P+115)+((310*P+112)+5)))) := by
    unfold withinCoefficientFromSource
    refine (withinSimilaritySetup_do (w := w) st hs ht hst hsV htV hdenV).seq
      (fun s₀ h₀ => ?_)
    have hf₀ (r : Fin 48) (hr44 : r ≠ 44) (hr47 : r ≠ 47) := h₀.2.2.2 r hr44 hr47
    have hsample₁ : TblDo A V w (.ins (.copy 26 41)) s₀ (fun s₁ =>
        s₁.val 41 = similarityGridNumerator P s t u j ∧ s₁.acc = s₀.acc ∧
        s₁.val 18 = s₀.val 18 ∧ s₁.val 19 = s₀.val 19 ∧ s₁.val 22 = s₀.val 22 ∧
        ∀ r : Fin 48, 34 ≤ r.val → r ≠ 45 → r ≠ 46 → r ≠ 41 → s₁.val r = s₀.val r) 1 := by
      apply TblDo.insX (.copy 26 41) trivial
      simp [TblIns.exact,hf₀ 26 (by decide) (by decide),hsource]
      intro r _ _ _ hr
      simp [hr]
    refine hsample₁.seq (fun s₁ h₁ => ?_)
    have hf₁ (r : Fin 48) (hr : 34 ≤ r.val) (hr45 : r ≠ 45) (hr46 : r ≠ 46)
        (hr41 : r ≠ 41) := h₁.2.2.2.2.2 r hr hr45 hr46 hr41
    have hsample₂ := similaritySampleAt_do (w := w) true s₁
      (h₁.2.2.1.trans (by rw [hf₀ 18 (by decide) (by decide)]; exact hpi))
      (h₁.2.2.2.1.trans (by rw [hf₀ 19 (by decide) (by decide)]; exact hP'))
      (h₁.2.2.2.2.1.trans (by rw [hf₀ 22 (by decide) (by decide)]; exact hneg))
      (by simpa [hf₁ 34 (by decide) (by decide) (by decide) (by decide),hf₀ 34 (by decide) (by decide)] using hs)
      (by simpa [hf₁ 35 (by decide) (by decide) (by decide) (by decide),hf₀ 35 (by decide) (by decide)] using ht)
      (by simpa [hf₁ 36 (by decide) (by decide) (by decide) (by decide),hf₀ 36 (by decide) (by decide)] using hu)
      (by simpa [hf₁ 38 (by decide) (by decide) (by decide) (by decide),hf₀ 38 (by decide) (by decide)] using hk)
      (by rw [hf₁ 47 (by decide) (by decide) (by decide) (by decide)]; exact h₀.1)
      (by rw [hf₁ 44 (by decide) (by decide) (by decide) (by decide)]; exact h₀.2.1)
      hP hs0 hst hkV hsV hsq huV hV hak
    refine hsample₂.seq (fun s₂ h₂ => ?_)
    have hf₂ (r : Fin 48) (hr : 34 ≤ r.val) (hr45 : r ≠ 45) (hr46 : r ≠ 46)
        (hr42 : r ≠ 42) := h₂.2.2.2.2.2 r hr hr45 hr46 hr42
    have hlow (r : Fin 48) (hrlo : 34 ≤ r.val) (hrhi : r.val ≤ 40) : s₂.val r = st.val r := by
      rw [hf₂ r hrlo (by intro h; subst r; norm_num at hrhi)
        (by intro h; subst r; norm_num at hrhi) (by intro h; subst r; norm_num at hrhi),
        hf₁ r hrlo (by intro h; subst r; norm_num at hrhi)
        (by intro h; subst r; norm_num at hrhi) (by intro h; subst r; norm_num at hrhi),
        hf₀ r (by intro h; subst r; norm_num at hrhi) (by intro h; subst r; norm_num at hrhi)]
    have hdistance := distanceSample_do (w := w) s₂
      (h₂.2.2.1.trans (h₁.2.2.1.trans (by rw [hf₀ 18 (by decide) (by decide)]; exact hpi)))
      (h₂.2.2.2.1.trans (h₁.2.2.2.1.trans (by rw [hf₀ 19 (by decide) (by decide)]; exact hP')))
      (h₂.2.2.2.2.1.trans (h₁.2.2.2.2.1.trans (by rw [hf₀ 22 (by decide) (by decide)]; exact hneg)))
      ((hlow 34 (by decide) (by decide)).trans hs)
      ((hlow 35 (by decide) (by decide)).trans ht)
      ((hlow 36 (by decide) (by decide)).trans hu)
      ((hlow 37 (by decide) (by decide)).trans hj)
      ((hlow 38 (by decide) (by decide)).trans hk)
      hP hs0 hV hjbound hkbound hdV htdV hudV had
    refine hdistance.seq (fun s₃ h₃ => ?_)
    have hf₃ (r : Fin 48) (hr : 34 ≤ r.val) (hr45 : r ≠ 45) := h₃.2.2.2.2.2.2 r hr hr45
    have hem := withinGridEmit_do (w := w) (q := q) (P := P) s₃
      ((hf₃ 41 (by decide) (by decide)).trans
        ((hf₂ 41 (by decide) (by decide) (by decide) (by decide)).trans h₁.1))
      ((hf₃ 42 (by decide) (by decide)).trans h₂.1) h₃.1 h₃.2.1
      ((hf₃ 39 (by decide) (by decide)).trans ((hlow 39 (by decide) (by decide)).trans hq))
      ((hf₃ 40 (by decide) (by decide)).trans ((hlow 40 (by decide) (by decide)).trans hpowP))
      hprodV hnumV hdivV
    refine hem.mono (fun s₄ h₄ => ?_) le_rfl
    have hacc : s₃.acc = st.acc := h₃.2.2.1.trans (h₂.2.1.trans (h₁.2.1.trans h₀.2.2.1))
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [within_coefficient_word q P s t u band j k hs0 hst hjk hband]
      simpa only [rationalWord_nat_ratio,naturalDistance_eq_natAbs,hacc] using h₄.1
    · exact (h₄.2 18 (by decide) (by decide)).trans
        (h₃.2.2.2.1.trans (h₂.2.2.1.trans (h₁.2.2.1.trans
          (hf₀ 18 (by decide) (by decide)))))
    · exact (h₄.2 19 (by decide) (by decide)).trans
        (h₃.2.2.2.2.1.trans (h₂.2.2.2.1.trans (h₁.2.2.2.1.trans
          (hf₀ 19 (by decide) (by decide)))))
    · exact (h₄.2 22 (by decide) (by decide)).trans
        (h₃.2.2.2.2.2.1.trans (h₂.2.2.2.2.1.trans (h₁.2.2.2.2.1.trans
          (hf₀ 22 (by decide) (by decide)))))
    · intro r hrlo hrhi
      rw [h₄.2 r (by intro h; subst r; norm_num at hrhi) (by intro h; subst r; norm_num at hrhi),
        hf₃ r hrlo (by intro h; subst r; norm_num at hrhi),hlow r hrlo hrhi]
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
