module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightBody

/-! Generate all three binary powers needed by both weight encoders. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM

def weightScales : TblCode 48 := tblPow2 42 45 40 ;;
  (tblPow2 43 19 40 ;; tblPow2 44 41 40)

theorem weightScales_do {A V w q P : ℕ} (st : TblSt 48 A)
    (hq : st.val 45 = q) (hP : st.val 19 = P) (hsum : st.val 41 = q + P)
    (hqV : q < V) (hPV : P < V) (hsumV : q + P < V) :
    TblDo A V w weightScales st (fun s =>
      s.val 42 = 2 ^ q ∧ s.val 43 = 2 ^ P ∧ s.val 44 = 2 ^ (q + P) ∧
      s.acc = st.acc ∧
      ∀ k, k ∉ [(40 : Fin 48), 42, 43, 44] → s.val k = st.val k) (8 * (q + P) + 15) := by
  have h₁ := tblPow2_do (A := A) (W := V) (w := w)
    (c := (42 : Fin 48)) (e := 45) (i := 40) (by decide) (by decide) (by decide)
    st (by omega)
  rw [hq] at h₁
  have hcore : TblDo A V w weightScales st (fun s =>
      s.val 42 = 2 ^ q ∧ s.val 43 = 2 ^ P ∧ s.val 44 = 2 ^ (q + P) ∧
      s.acc = st.acc ∧
      ∀ k, k ∉ [(40 : Fin 48), 42, 43, 44] → s.val k = st.val k)
      ((4 * q + 5) + ((4 * P + 5) + (4 * (q + P) + 5))) := by
    unfold weightScales
    refine h₁.seq (fun s₁ ⟨g42, _, hf₁, ha₁⟩ => ?_)
    have he₁ : s₁.val 19 = P := (hf₁ 19 (by decide) (by decide)).trans hP
    have hs₁ : s₁.val 41 = q + P := (hf₁ 41 (by decide) (by decide)).trans hsum
    have h₂ := tblPow2_do (A := A) (W := V) (w := w)
      (c := (43 : Fin 48)) (e := 19) (i := 40) (by decide) (by decide) (by decide)
      s₁ (by omega)
    rw [he₁] at h₂
    refine h₂.seq (fun s₂ ⟨g43, _, hf₂, ha₂⟩ => ?_)
    have hs₂ : s₂.val 41 = q + P := (hf₂ 41 (by decide) (by decide)).trans hs₁
    have h₃ := tblPow2_do (A := A) (W := V) (w := w)
      (c := (44 : Fin 48)) (e := 41) (i := 40) (by decide) (by decide) (by decide)
      s₂ (by omega)
    rw [hs₂] at h₃
    refine h₃.mono (fun s₃ ⟨g44, _, hf₃, ha₃⟩ => ?_) le_rfl
    refine ⟨?_, ?_, g44, ha₃.trans (ha₂.trans ha₁), ?_⟩
    · exact (hf₃ 42 (by decide) (by decide)).trans
        ((hf₂ 42 (by decide) (by decide)).trans g42)
    · exact (hf₃ 43 (by decide) (by decide)).trans g43
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      exact (hf₃ k hk.2.2.2 hk.1).trans ((hf₂ k hk.2.2.1 hk.1).trans (hf₁ k hk.2.1 hk.1))
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
