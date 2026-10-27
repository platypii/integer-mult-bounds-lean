module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloMembershipMask
public import IntegerMultBounds.NLogN.PhaseCellHaloExterior

/-! Compute a nonwrapping exterior-stencil bit from the doubled guard-band header. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def exteriorMaskPrefix : List (TblIns 16) :=
  [.zero 6,.inc 6,.inc 6,.div 2 6 7,.add 3 7 8,.add 5 7 9,.zero 10,.inc 10]

def exteriorMaskBranch : TblCode 16 :=
  .ite 3 7 (.ins (.zero 15))
    (.ite 8 0 (.ite 8 4 (.ins (.copy 10 15))
      (.ite 3 9 (.ins (.zero 15)) (.ins (.copy 10 15)))) (.ins (.zero 15)))

def exteriorMaskCode : TblCode 16 := tblBlock 16 exteriorMaskPrefix (.zero 15) ;; exteriorMaskBranch

theorem exteriorMaskCode_do {A V w s B a b k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hband : st.val 2 = B) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hks : k < s) (hbS : b ≤ s)
    (hwide : 2*s+2*B+8 < 2^V) :
    TblDo A V w exteriorMaskCode st (fun st' =>
      st'.val 15 = (if haloExteriorAt s (B/2) a b k then 1 else 0) ∧ st'.acc = st.acc ∧
      ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 14 := by
  have hV : V ≠ 0 := by intro h; subst V; norm_num at hwide <;> omega
  let R := B/2
  have hR : R ≤ B := Nat.div_le_self _ _
  let S₀ := tblExactList A w (exteriorMaskPrefix++[.zero 15]) st
  have hp : TblDo A V w (tblBlock 16 exteriorMaskPrefix (.zero 15)) st (fun st' => st' = S₀) 9 := by
    apply TblDo.block
    · simp [exteriorMaskPrefix,tblFitsList,TblIns.fits,TblIns.exact,hband,hk,hb,hV]
      omega
    · rfl
  have hv0 : S₀.val 0 = s := by simp [S₀,exteriorMaskPrefix,tblExactList,TblIns.exact,hs]
  have hv3 : S₀.val 3 = k := by simp [S₀,exteriorMaskPrefix,tblExactList,TblIns.exact,hk]
  have hv4 : S₀.val 4 = a := by simp [S₀,exteriorMaskPrefix,tblExactList,TblIns.exact,ha]
  have hv7 : S₀.val 7 = R := by simp [S₀,exteriorMaskPrefix,tblExactList,TblIns.exact,hband,R]
  have hv8 : S₀.val 8 = k+R := by simp [S₀,exteriorMaskPrefix,tblExactList,TblIns.exact,hband,hk,R]
  have hv9 : S₀.val 9 = b+R := by simp [S₀,exteriorMaskPrefix,tblExactList,TblIns.exact,hband,hb,R]
  have hv10 : S₀.val 10 = 1 := by simp [S₀,exteriorMaskPrefix,tblExactList,TblIns.exact]
  have hacc : S₀.acc = st.acc := rfl
  have hlow (r : Fin 16) (hr : r.val < 6) : S₀.val r = st.val r := by
    have hn : r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 15 := by
      simp only [ne_eq,Fin.ext_iff]; omega
    simp [S₀,exteriorMaskPrefix,tblExactList,TblIns.exact,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2]
  let Post := fun st' : TblSt 16 A =>
    st'.val 15 = (if haloExteriorAt s R a b k then 1 else 0) ∧ st'.acc = st.acc ∧
    ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r
  have hz (h : haloExteriorAt s R a b k = false) : TblDo A V w (.ins (.zero 15)) S₀ Post 1 := by
    apply TblDo.insX (.zero 15) (by simp [TblIns.fits])
    refine ⟨by simp [TblIns.exact,h],hacc,?_⟩
    intro r hr
    have hn : r ≠ 15 := by intro he; subst r; norm_num at hr
    simpa [TblIns.exact,hn] using hlow r hr
  have ho (h : haloExteriorAt s R a b k = true) : TblDo A V w (.ins (.copy 10 15)) S₀ Post 1 := by
    apply TblDo.insX (.copy 10 15) (by simp [TblIns.fits])
    refine ⟨by simp [TblIns.exact,h,hv10],hacc,?_⟩
    intro r hr
    have hn : r ≠ 15 := by intro he; subst r; norm_num at hr
    simpa [TblIns.exact,hn] using hlow r hr
  have hc : TblDo A V w exteriorMaskBranch S₀ Post 5 := by
    unfold exteriorMaskBranch
    by_cases hlo : k < R
    · exact (TblDo.iteT (by simpa [hv3,hv7] using hlo)
        (hz (by simp [haloExteriorAt,show ¬R ≤ k by omega]))).mono (fun _ h => h) (by omega)
    · apply TblDo.iteF (by simpa [hv3,hv7] using hlo)
      by_cases hhi : k+R < s
      · apply TblDo.iteT (by simpa [hv8,hv0] using hhi)
        by_cases hbefore : k+R < a
        · exact (TblDo.iteT (by simpa [hv8,hv4] using hbefore)
            (ho (by simp [haloExteriorAt,show R ≤ k by omega,hhi,hbefore]))).mono (fun _ h => h) (by omega)
        · apply TblDo.iteF (by simpa [hv8,hv4] using hbefore)
          by_cases hafter : k < b+R
          · exact TblDo.iteT (by simpa [hv3,hv9] using hafter)
              (hz (by simp [haloExteriorAt,hbefore,show ¬b+R ≤ k by omega]))
          · exact TblDo.iteF (by simpa [hv3,hv9] using hafter)
              (ho (by simp [haloExteriorAt,show R ≤ k by omega,hhi,show b+R ≤ k by omega]))
      · exact (TblDo.iteF (by simpa [hv8,hv0] using hhi)
          (hz (by simp [haloExteriorAt,hhi]))).mono (fun _ h => h) (by omega)
  exact hp.seq (fun st' he => by subst st'; exact hc)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
