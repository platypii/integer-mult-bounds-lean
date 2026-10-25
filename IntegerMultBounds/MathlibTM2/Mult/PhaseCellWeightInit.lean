module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightScales

/-! Generate pi, similarity geometry and binary scale values before the weight
loop. Only ordinary numeric geometry, precision and coordinate headers remain
as setup inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def weightInitCode : TblCode 48 := tblPiSetup48 ;; (weightGeometry ;; weightScales)

def WeightInitialized {A : ℕ} (st : TblSt 48 A) (P q s t : ℕ) : Prop :=
  st.val 18 = piN P ∧ st.val 22 = 1 ∧ st.val 38 = 2 * s ∧
    st.val 39 = similarityDenominator s t ∧ st.val 42 = 2 ^ q ∧
    st.val 43 = 2 ^ P ∧ st.val 44 = 2 ^ (q + P)

/-- Source headers and the accumulator survive all initialization stages. -/
theorem weightInitCode_do {A V w P q s t : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hq : st.val 45 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hst : s ≤ t)
    (hP : 13 ≤ P) (hV : 13 * P + 8 ≤ V) (hqV : q + P + 2 ≤ V)
    (hsV : 2 * s < 2 ^ V) (htV : t < 2 ^ V)
    (hdV : similarityDenominator s t < 2 ^ V) :
    TblDo A V w weightInitCode st (fun st' =>
      WeightInitialized st' P q s t ∧ st'.acc = st.acc ∧
      ∀ k : Fin 48, 19 ≤ k.val → k ∉ [(22 : Fin 48), 38, 39, 40, 41, 42, 43, 44] →
        st'.val k = st.val k) (158 * P + 8 * q + 424) := by
  have hpqV : q + P < 2 ^ V :=
    (show q + P < V by omega).trans (show V < 2 ^ V from Nat.lt_two_pow_self)
  have hpi := tbl_pi48_do (A := A) (W := V) (w := w) st hP' (by omega) (by omega)
  have hcore : TblDo A V w weightInitCode st (fun st' =>
      WeightInitialized st' P q s t ∧ st'.acc = st.acc ∧
      ∀ k : Fin 48, 19 ≤ k.val → k ∉ [(22 : Fin 48), 38, 39, 40, 41, 42, 43, 44] →
        st'.val k = st.val k) ((1 + (150 * P + 400)) + (8 + (8 * (q + P) + 15))) := by
    unfold weightInitCode
    refine hpi.seq (fun s₁ ⟨gp, ga, gf⟩ => ?_)
    have hg := weightGeometry_do (A := A) (V := V) (w := w) s₁
      ((gf 19 (by decide)).trans hP') ((gf 45 (by decide)).trans hq)
      ((gf 34 (by decide)).trans hs) ((gf 35 (by decide)).trans ht)
      hst (by omega) hsV htV hdV hpqV
    refine hg.seq (fun s₂ ⟨g22, g38, g39, g41, ga₂, gf₂⟩ => ?_)
    have hp₂ : s₂.val 19 = P := (gf₂ 19 (by simp)).trans ((gf 19 (by decide)).trans hP')
    have hq₂ : s₂.val 45 = q := (gf₂ 45 (by simp)).trans ((gf 45 (by decide)).trans hq)
    refine (weightScales_do (A := A) (V := V) (w := w) s₂ hq₂ hp₂ g41
      (by omega) (by omega) (by omega)).mono ?_ le_rfl
    intro s₃ ⟨g42, g43, g44, ga₃, gf₃⟩
    refine ⟨⟨?_, ?_, ?_, ?_, g42, g43, g44⟩, ga₃.trans (ga₂.trans ga), ?_⟩
    · exact (gf₃ 18 (by simp)).trans ((gf₂ 18 (by simp)).trans gp)
    · exact (gf₃ 22 (by simp)).trans g22
    · exact (gf₃ 38 (by simp)).trans g38
    · exact (gf₃ 39 (by simp)).trans g39
    · intro k hk hnot
      have hn₂ : k ∉ [(22 : Fin 48), 38, 39, 40, 41] := by
        intro hm; exact hnot (by simp_all)
      have hn₃ : k ∉ [(40 : Fin 48), 42, 43, 44] := by
        intro hm; exact hnot (by simp_all)
      exact (gf₃ k hn₃).trans ((gf₂ k hn₂).trans (gf k hk))
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
