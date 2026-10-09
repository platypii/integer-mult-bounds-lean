import IntegerMultBounds.Machine.CountedRepairKeyRun

/-! Rank membership and destination key bridges for actual short counters. -/
namespace IntegerMultBounds.Machine.CountedRepairKeyValue
noncomputable section
open CountedRepairKeyBank
open CountedRankSplitData (field_append_zero value_append_zero)
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo

theorem flag_rank (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z cs : List Bool)
    (j : ℕ) (hj : j<Mi q b Z) (hc : Counter.value cs=j) :
    flag q b (V q Z cs) (W q b Z cs) Z = rankFlag (rankEquiv q b Z) (badSet q b Z) j := by
  obtain ⟨h1,h2,h3⟩ := CountedGuardConstantsData.lengths q b hb hbq
  obtain ⟨v1,v2,v3⟩ := CountedGuardConstantsData.values q b hb hbq
  have h := flag_bridge q b hbq Z (cs++List.replicate (Z.length*q+Z.length*b) false)
    (CountedGuardConstantsData.c1 q b) (CountedGuardConstantsData.c2 q b) (CountedGuardConstantsData.c3 b)
    h1 h2 h3 v1 v2 v3 j hj (by rw [value_append_zero,hc]) (by simp)
  simpa only [flag,CountedGuardGadget.flags,V,W,Vw,Ww,field_append_zero] using h

theorem bits_rank (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (Z cs : List Bool)
    (j : ℕ) (hj : j<Mi q b Z) (hc : Counter.value cs=j) :
    CountedRepairKeyRun.bits q b hb hbq (V q Z cs) (W q b Z cs) Z =
      rankKey (rankEquiv q b Z) (Sperm q b Z) (Tperm q b Z) (Z.length*q+Z.length*b) j := by
  have h := bits_bridge q b hb hbq Z (cs++List.replicate (Z.length*q+Z.length*b) false)
    (by omega) j hj (by rw [value_append_zero,hc]) (by simp)
  simp only [Vw,Ww,field_append_zero,ColumnTransducer.xorRule_digits,map_zip_xor,gather_controls] at h
  exact h.symm

end
end IntegerMultBounds.Machine.CountedRepairKeyValue
