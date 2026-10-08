import IntegerMultBounds.Machine.RecursiveAffinePrepare

/-! Paid cross-group coordinate-view preparation on the same positive runtime
layout. The role divisor is physically initialized to one, so every payload
row survives. No root-path or power-width certificate is needed beyond the
actual width factorization used by this fixed field operation. -/
namespace IntegerMultBounds.Machine.RecursiveCrossPrepare
open RecursiveInterchangeLayout (Descriptor child volume)
variable {q : ℕ}
noncomputable section

def program (hq : 2 ≤ q) {m : ℕ} (i j : Fin m) := RecursiveChildPrepare.program hq 1 i j

def constant (m : ℕ) := RecursiveAffinePrepare.quotientConstant m+97*(48*(m-1)+512)+11900

theorem prepares (hq : 2 ≤ q) (b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width=m*b) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (RecursiveAffineViews.cross q b v i j) ch ∧
      HoareTime (program hq i j)
        (fun w => w = RecursiveChildHeaderHandoff.canonical hs)
        (fun w => w = RecursiveChildHeaderHandoff.canonical ch) (constant m*volume q v) := by
  have hm : 0 < m := by have hi := i.isLt; omega
  obtain ⟨bs,rs,cb,cr,hb,hr,hquot⟩ := RecursiveChildQuotients.quotients_hoare (a := q) m 1 hm (by decide) hs
  have hb' : Counter.value bs = b := by
    rw [show Counter.value (hs 3) = v.width from hv.1 3,hw,Nat.mul_div_right b hm] at hb
    exact hb
  have hr' : Counter.value rs = v.rows/1 := by
    rw [show Counter.value (hs 1) = v.rows from hv.1 1] at hr
    exact hr
  let ch := RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j
  have hch : RecursiveDimensionBank.Headers (child q 1 b v i j) ch :=
    RecursiveChildDimensions.child_headers 1 b v hs bs rs i j hv hb' cb hr' cr
  have hview : (child q 1 b v i j).Positive := by
    rcases hp with ⟨hA,hR,hB,hC,hE⟩
    have hq' : 0 < q := by omega
    dsimp [Descriptor.Positive,child]
    rw [Nat.div_one]
    exact ⟨hA,hR,Nat.mul_pos hB (pow_pos hq' _),
      Nat.mul_pos (Nat.mul_pos (pow_pos hq' _) hC) (pow_pos hq' _),Nat.mul_pos (pow_pos hq' _) hE⟩
  have hvol : volume q (child q 1 b v i j) = volume q v := RecursiveAffineViews.cross_volume q b v i j hw
  have hV := RecursiveAffinePrepare.volume_positive hq v hp
  have hold (z : Fin 6) : (hs z).length ≤ 2*volume q v := by
    have hh := RecursiveAffinePrepare.header_log hq v hp hs hv z
    have hl := Nat.log2_le_self (volume q v)
    omega
  have hnew (z : Fin 6) : (ch z).length ≤ 2*volume q v := by
    have hh := RecursiveAffinePrepare.header_log hq _ hview ch hch z
    rw [hvol] at hh
    have hl := Nat.log2_le_self (volume q v)
    omega
  have hc := RecursiveChildHeaderHandoff.constructs_hoare hq 1 b v hs bs rs i j hv hp hb' cb (by decide) (one_dvd _)
  rw [hvol] at hc
  have hh := hquot.seq hc
  rw [RecursiveChildPrepare.input_eq] at hh
  refine ⟨ch,hch,hh.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  have hqc := RecursiveAffinePrepare.quotient_cost hq v hp m hs hv
  have hhc := RecursiveChildHeaderHandoff.cost_le hs ch (2*volume q v) hold hnew
  unfold constant
  change RecursiveChildQuotients.cost m 1 hs+1+(97*(48*(m-1)+512)*volume q v+11756+1+
    RecursiveChildHeaderHandoff.cost hs ch) ≤ _
  nlinarith

end
end IntegerMultBounds.Machine.RecursiveCrossPrepare
