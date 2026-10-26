module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalDistance

/-! Construct the Gaussian distance argument from retained natural coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def distanceArgument : TblCode 48 :=
  naturalDistanceCode 37 38 45 ;;
    tblBlock 48 [.mul 45 45 20, .mul 35 20 20, .mul 36 20 20] (.copy 34 21)

theorem distanceArgument_do {A V w s t u j k : ℕ} (st : TblSt 48 A)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = j) (hk : st.val 38 = k)
    (hjV : j < 2^V) (hkV : k < 2^V)
    (hdV : naturalDistance j k ^ 2 < 2^V)
    (htV : t * naturalDistance j k ^ 2 < 2^V)
    (huV : u * (t * naturalDistance j k ^ 2) < 2^V) :
    TblDo A V w distanceArgument st (fun st' =>
      st'.val 20 = u*t*naturalDistance j k^2 ∧ st'.val 21 = s ∧
      st'.acc = st.acc ∧
      ∀ r, r ∉ [(20 : Fin 48),21,45] → st'.val r = st.val r) 6 := by
  simp only [pow_two] at hdV htV huV
  unfold distanceArgument
  refine (naturalDistanceCode_do (w := w) 37 38 45 st hj hk hjV hkV).seq
    (K₂ := 4) (fun s₁ h₁ => ?_)
  subst s₁
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,ht,hu,hdV,htV,huV]
  · simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
    simp [hs,ht,hu,pow_two,Nat.mul_assoc]
    intro r hr20 hr21 hr45
    simp [hr20,hr21,hr45]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
