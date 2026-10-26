module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalDistance
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientExp

/-! Execute the direct lattice exponent from ordinary natural coordinates.
All subtraction and multiplication bounds precede the corresponding instructions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def latticeArgumentPrefix : List (TblIns 48) :=
  [.add 34 34 41, .mul 35 37 47, .add 47 47 47, .add 47 34 47, .div 47 41 42,
    .mul 35 38 44, .add 44 44 47, .add 47 34 47, .div 47 41 43,
    .mul 34 42 45]

def latticeArgument : TblCode 48 :=
  tblBlock 48 latticeArgumentPrefix (.mul 34 43 46) ;; (naturalDistanceCode 44 45 45 ;;
    (naturalDistanceCode 44 46 46 ;; tblBlock 48
      [.mul 45 45 45, .mul 46 46 46, .sub 45 46 20, .mul 36 20 20] (.mul 34 34 21)))

theorem latticeArgument_do {A V w s t u j k : ℕ} (st : TblSt 48 A)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = j) (hk : st.val 38 = k) (hs0 : 0 < s) (hst : s < t)
    (hjV : 2*t*j+s < 2^V) (hkV : 2*t*k+s < 2^V) (hsV : 2*s < 2^V)
    (hnjV : s*nearestNatural s t j < 2^V) (hnkV : s*nearestNatural s t k < 2^V)
    (hdjV : latticeDistance s t j k^2 < 2^V) (hdkV : latticeDistance s t k k^2 < 2^V)
    (hnumV : latticeNumerator s t u j k < 2^V) (hsqV : s^2 < 2^V) :
    TblDo A V w latticeArgument st (fun st' =>
      st'.val 20 = latticeNumerator s t u j k ∧ st'.val 21 = s^2 ∧ st'.acc = st.acc ∧
      ∀ r : Fin 48, r.val ≤ 40 → r ≠ 20 → r ≠ 21 → st'.val r = st.val r) 20 := by
  let S₁ : TblSt 48 A := ⟨Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update st.val 41 (2*s)) 47 (2*t*k+s))
      42 (nearestNatural s t j)) 43 (nearestNatural s t k)) 44 (t*k))
      45 (s*nearestNatural s t j)) 46 (s*nearestNatural s t k),st.acc⟩
  have htjV : t*j < 2^V := by nlinarith only [hjV]
  have htkV : t*k < 2^V := by nlinarith only [hkV]
  have hp : TblDo A V w (tblBlock 48 latticeArgumentPrefix (.mul 34 43 46)) st (fun st' => st' = S₁) 11 := by
    apply TblDo.block
    · simp only [Nat.mul_assoc] at hjV hkV
      simp [latticeArgumentPrefix,tblFitsList,TblIns.fits,TblIns.exact,hs,ht,hu,hj,hk,
        nearestNatural,← two_mul,Nat.mul_assoc] at hnjV hnkV ⊢
      omega
    · simp [latticeArgumentPrefix,tblExactList,TblIns.exact,S₁,hs,ht,hu,hj,hk,
        nearestNatural,← two_mul,Nat.mul_assoc]
      funext r
      by_cases h47 : r = 47
      · subst r; simp [Nat.mul_assoc]
      by_cases h44 : r = 44
      · subst r; simp [Nat.mul_assoc]
      simp [Function.update_apply,h47,h44,Nat.mul_assoc]
  obtain hd₁ := naturalDistanceCode_do (A := A) (V := V) (w := w) (a := t*k) (b := s*nearestNatural s t j) 44 45 45 S₁
    (by simp [S₁]) (by simp [S₁]) htkV hnjV
  let S₂ : TblSt 48 A := ⟨Function.update S₁.val 45 (latticeDistance s t j k),st.acc⟩
  have hd₁' : TblDo A V w (naturalDistanceCode 44 45 45) S₁ (fun st' => st' = S₂) 2 := by
    simpa only [S₂,S₁,latticeDistance] using hd₁
  obtain hd₂ := naturalDistanceCode_do (A := A) (V := V) (w := w) (a := t*k) (b := s*nearestNatural s t k) 44 46 46 S₂
    (by simp [S₂,S₁]) (by simp [S₂,S₁]) htkV hnkV
  let S₃ : TblSt 48 A := ⟨Function.update S₂.val 46 (latticeDistance s t k k),st.acc⟩
  have hd₂' : TblDo A V w (naturalDistanceCode 44 46 46) S₂ (fun st' => st' = S₃) 2 := by
    simpa only [S₃,S₂,S₁,latticeDistance] using hd₂
  let S₄ : TblSt 48 A := ⟨Function.update (Function.update (Function.update (Function.update
    S₃.val 45 (latticeDistance s t j k^2)) 46 (latticeDistance s t k k^2))
      20 (latticeNumerator s t u j k)) 21 (s^2),st.acc⟩
  have he : TblDo A V w (tblBlock 48
      [.mul 45 45 45, .mul 46 46 46, .sub 45 46 20, .mul 36 20 20] (.mul 34 34 21))
      S₃ (fun st' => st' = S₄) 5 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,S₃,S₂,S₁,hs,hu,← pow_two,
        hdjV,hdkV,hsqV,latticeDistance_sq_le s t j k hs0 hst]
      simpa only [latticeNumerator] using hnumV
    · simp [tblExactList,TblIns.exact,S₄,S₃,S₂,S₁,hs,hu,latticeNumerator,pow_two]
  have hcore : TblDo A V w latticeArgument st (fun st' => st' = S₄) 20 := by
    unfold latticeArgument
    exact hp.seq (fun st' h => h ▸ hd₁'.seq (fun st'' h' => h' ▸ hd₂'.seq (fun st''' h'' => h'' ▸ he)))
  refine hcore.mono (fun st' h => ?_) le_rfl
  subst st'
  refine ⟨by simp [S₄],by simp [S₄],rfl,?_⟩
  intro r hr hr20 hr21
  have hn (n : ℕ) (hn : 41 ≤ n) : r.val ≠ n := by omega
  simp [S₄,S₃,S₂,S₁,hr20,hr21,Fin.ext_iff,hn 41 (by decide),hn 42 (by decide),
    hn 43 (by decide),hn 44 (by decide),hn 45 (by decide),hn 46 (by decide),hn 47 (by decide)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
