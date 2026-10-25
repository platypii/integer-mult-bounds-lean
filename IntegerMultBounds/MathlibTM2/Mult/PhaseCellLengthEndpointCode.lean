module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalIntervalCode

/-! Compute and emit the two clipped endpoint lengths using the same interval
arithmetic as the executed natural phase scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem emitCurrentLength_do {A W e L : ℕ} (st : TblSt 16 A)
    (hL : st.val 11 = L) (hz : st.val 12 = 0) :
    TblDo A W e (.ins (.emit 11 12)) st (fun st' => st'.val = st.val ∧
      st'.acc = (tblPairs A e L 0).reverse ++ st.acc) 1 :=
  TblDo.ins _ (by simp [TblIns.run, hL, hz])

def naturalEndpointLengthsCode : TblCode 16 :=
  naturalIntervalCode ;; (.ins (.emit 11 12) ;; (.ins (.sub 1 0 4) ;;
    (naturalIntervalCode ;; .ins (.emit 11 12))))

theorem naturalEndpointLengthsCode_do {A W e s t band : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (hphase : st.val 4 = 0) (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hs : 0 < s) (hst : s < t) (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W e naturalEndpointLengthsCode st (fun st' => st'.val 4 = t-s ∧
      st'.acc = (tblPairs A e (naturalLength s t band 0) 0 ++
        tblPairs A e (naturalLength s t band (t-s)) 0).reverse ++ st.acc ∧
      ∀ k, k ∉ [(4 : Fin 16), 8, 9, 10, 11] → st'.val k = st.val k) 45 := by
  have htW : t < 2^W := by nlinarith only [hwide]
  have h₀ := naturalIntervalCode_do (A := A) (W := W) (w := e) st hs' hband hphase hden hone hs hst
    (by omega : 0 ≤ t-s) hwide
  unfold naturalEndpointLengthsCode
  apply h₀.seq (K₂ := 24)
  intro st₁ ⟨_, _, hl₁, ha₁, hf₁⟩
  have hz₁ := (hf₁ 12 (by simp)).trans hz
  apply (emitCurrentLength_do (W := W) (e := e) st₁ hl₁ hz₁).seq (K₂ := 23)
  intro st₂ ⟨hv₂, ha₂⟩
  have hs₂ : st₂.val 0 = s := by rw [hv₂]; exact (hf₁ 0 (by simp)).trans hs'
  have ht₂ : st₂.val 1 = t := by rw [hv₂]; exact (hf₁ 1 (by simp)).trans ht
  let S₃ : TblSt 16 A := ⟨Function.update st₂.val 4 (t-s), st₂.acc⟩
  have hsub : TblDo A W e (.ins (.sub 1 0 4)) st₂ (fun st' => st' = S₃) 1 := by
    apply TblDo.insX
    · simp [TblIns.fits, hs₂, ht₂, hst.le, htW]
    · simp [TblIns.exact, S₃, hs₂, ht₂]
  apply hsub.seq (K₂ := 22)
  intro st₃ he₃
  subst he₃
  have hlast := naturalIntervalCode_do (A := A) (W := W) (w := e) S₃
    (by simpa [S₃] using hs₂) (by simp [S₃, hv₂, hf₁ 2 (by simp), hband]) (by simp [S₃])
    (by simp [S₃, hv₂, hf₁ 6 (by simp), hden]) (by simp [S₃, hv₂, hf₁ 7 (by simp), hone])
    hs hst le_rfl hwide
  apply hlast.seq (K₂ := 1)
  intro st₄ ⟨_, _, hl₄, ha₄, hf₄⟩
  have hz₄ : st₄.val 12 = 0 := by rw [hf₄ 12 (by simp)]; simp [S₃, hv₂, hf₁ 12 (by simp), hz]
  exact (emitCurrentLength_do (W := W) (e := e) st₄ hl₄ hz₄).mono (fun st₅ ⟨hv₅, ha₅⟩ => by
    refine ⟨by rw [hv₅, hf₄ 4 (by simp)]; simp [S₃], ?_, ?_⟩
    · rw [ha₅, ha₄]
      simp [S₃, ha₂, ha₁, List.reverse_append, List.append_assoc]
    · intro k hk
      have hk4 : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
      have hkr : k ∉ [(8 : Fin 16), 9, 10, 11] := fun hm => hk (List.mem_cons_of_mem 4 hm)
      rw [hv₅, hf₄ k hkr]
      simp [S₃, hk4, hv₂, hf₁ k hkr]) (by decide)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
