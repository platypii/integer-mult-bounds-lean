module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightBody

/-! Generate similarity geometry and scale-exponent headers from ordinary
numeric inputs. Subtraction runs only for a strictly expanding ratio. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def weightGeometry : TblCode 48 :=
  tblBlock 48 [.zero 22, .inc 22, .add 34 34 38, .sub 35 34 40,
    .mul 34 40 39, .add 39 39 39, .add 39 39 39] (.add 45 19 41)

theorem weightGeometry_do {A V w P q s t : ℕ} (st : TblSt 48 A)
    (hP : st.val 19 = P) (hq : st.val 45 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hst : s ≤ t)
    (hV : 0 < V) (hsV : 2 * s < 2 ^ V) (htV : t < 2 ^ V)
    (hdV : similarityDenominator s t < 2 ^ V) (hpqV : q + P < 2 ^ V) :
    TblDo A V w weightGeometry st (fun st' =>
      st'.val 22 = 1 ∧ st'.val 38 = 2 * s ∧
      st'.val 39 = similarityDenominator s t ∧ st'.val 41 = q + P ∧
      st'.acc = st.acc ∧
      ∀ k, k ∉ [(22 : Fin 48), 38, 39, 40, 41] → st'.val k = st.val k) 8 := by
  have he : s * (t - s) + s * (t - s) + (s * (t - s) + s * (t - s)) =
      similarityDenominator s t := by unfold similarityDenominator; ring
  have hbase : s * (t - s) < 2 ^ V := by omega
  have htwo : s * (t - s) + s * (t - s) < 2 ^ V := by omega
  have hone : 1 < 2 ^ V := Nat.one_lt_two_pow (by omega)
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hP, hq, hs, ht,
      hst, htV, hbase, htwo, he, hdV, hpqV, hone]
    omega
  · simp [tblExactList, TblIns.exact, hP, hq, hs, ht, he, two_mul]
    intro k hk22 hk38 hk39 hk40 hk41
    simp [hk22, hk38, hk39, hk40, hk41]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
