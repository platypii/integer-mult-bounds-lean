module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLatticeArgument

/-! Compare phases without signed subtraction: nearest(j)+k = nearest(k)+j. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def phaseArguments : TblCode 48 :=
  tblBlock 48 [.add 34 34 41,
    .mul 35 37 42, .add 42 42 42, .add 42 34 42, .div 42 41 42, .add 42 38 42,
    .mul 35 38 43, .add 43 43 43, .add 43 34 43, .div 43 41 43] (.add 43 37 43)

theorem phaseArguments_do {A V w s t j k : ℕ} (st : TblSt 48 A)
    (hs : st.val 34 = s) (ht : st.val 35 = t)
    (hj : st.val 37 = j) (hk : st.val 38 = k)
    (hsV : 2*s < 2^V) (hjV : 2*t*j+s < 2^V) (hkV : 2*t*k+s < 2^V)
    (hjkV : nearestNatural s t j+k < 2^V) (hkjV : nearestNatural s t k+j < 2^V) :
    TblDo A V w phaseArguments st (fun st' =>
      st'.val 42 = nearestNatural s t j+k ∧ st'.val 43 = nearestNatural s t k+j ∧
      st'.acc = st.acc ∧ ∀ r, r ∉ [(41 : Fin 48),42,43] → st'.val r = st.val r) 11 := by
  have htjV : t*j < 2^V := by nlinarith only [hjV]
  have htkV : t*k < 2^V := by nlinarith only [hkV]
  dsimp only [nearestNatural] at hjkV hkjV
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hs,ht,hj,hk,← two_mul,
      ← Nat.mul_assoc,nearestNatural,hjkV,hkjV]
    omega
  · simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
    simp [hs,ht,hj,hk,← two_mul,← Nat.mul_assoc,nearestNatural]
    intro r hr41 hr42 hr43
    simp [hr41,hr42,hr43]

theorem phaseArguments_eq_iff (s t j k : ℕ) :
    nearestNatural s t j+k = nearestNatural s t k+j ↔
      PhaseCellCrossCell.phaseQ s t j = PhaseCellCrossCell.phaseQ s t k := by
  have hnear (i : ℕ) : PhaseCellRationalArgs.nearestQ s t i = (nearestNatural s t i : ℤ) := by
    simp only [PhaseCellRationalArgs.nearestQ,nearestNatural]
    norm_cast
  simp only [PhaseCellCrossCell.phaseQ,hnear]
  constructor
  · intro he
    have heZ := congrArg (fun x : ℕ => (x : ℤ)) he
    push_cast at heZ
    omega
  · intro he
    have heZ : (nearestNatural s t j : ℤ)+k = (nearestNatural s t k : ℤ)+j := by omega
    exact_mod_cast heZ

/-- Equality branches use the two strict comparisons supplied by the table VM. -/
def tableIfEq {n : ℕ} (x y : Fin n) (yes no : TblCode n) : TblCode n :=
  .ite x y no (.ite y x no yes)

theorem tableIfEq_do {n A V w K : ℕ} (x y : Fin n) (yes no : TblCode n)
    (st : TblSt n A) (Post : TblSt n A → Prop)
    (hyes : st.val x = st.val y → TblDo A V w yes st Post K)
    (hno : st.val x ≠ st.val y → TblDo A V w no st Post K) :
    TblDo A V w (tableIfEq x y yes no) st Post (K+2) := by
  unfold tableIfEq
  by_cases hxy : st.val x < st.val y
  · exact (TblDo.iteT hxy (hno (by omega))).mono (fun _ h => h) (by omega)
  · apply TblDo.iteF hxy
    by_cases hyx : st.val y < st.val x
    · exact TblDo.iteT hyx (hno (by omega))
    · exact TblDo.iteF hyx (hyes (by omega))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
