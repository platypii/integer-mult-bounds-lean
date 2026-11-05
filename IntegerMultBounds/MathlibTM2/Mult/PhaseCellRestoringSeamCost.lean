module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication
public import IntegerMultBounds.NLogN.PhaseCellBoundaryCropSchedule

/-! Aggregate the executed setup/publication/retirement bill by line volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellMatrix

def restoringSeamCost (w W N s a L : ℕ) : ℕ :=
  widenPackedPrefixCost w W (N*L)+replicaPublicationCost N s 0 L W+
    37*s*W+6*N+31+(6*(L*W)+6*W+13)+(1+(4*(a*W)+5))+
    (4*(a*W)+5)+(2*(1+L*W+W)+7)

theorem restoringSeamCost_le (w W N s a L : ℕ) (hs : 1 ≤ s) (hW : 1 ≤ W)
    (hw : w ≤ W) (ha : a ≤ s) (hL : L ≤ s) :
    restoringSeamCost w W N s a L ≤ 250*(N+1)*(s*W) := by
  have hwide := widenPackedPrefixCost_le_volume w W (N*L) hW hw
  have hpub := replicaPublicationCost_le N s 0 L W hs hW
  simp only [Nat.zero_mul,Nat.mul_zero,Nat.zero_add] at hpub
  have hLW := Nat.mul_le_mul_right W hL
  have haW := Nat.mul_le_mul_right W ha
  have hNLW := Nat.mul_le_mul_left N hLW
  have hvol : 1 ≤ s*W := Nat.mul_pos hs hW
  have hsmall : W ≤ s*W := by nlinarith
  have hN : N ≤ N*(s*W) := by nlinarith
  unfold restoringSeamCost
  nlinarith

/-- The boundary schedule has at most three entries; repeated or overlapping
cores require no extra arithmetic cases. -/
theorem restoringSeamCost_sum_le (w W N s width : ℕ) (ks : List ℕ)
    (hs : 1 ≤ s) (hW : 1 ≤ W) (hw : w ≤ W) (hcount : ks.length ≤ 3)
    (hstart : ∀ k ∈ ks, coreStart width k ≤ s) :
    (ks.map (fun k => restoringSeamCost w W N s
      (coreStart width k)
      (coreLength s width k))).sum ≤
        750*(N+1)*(s*W) := by
  have hsum : (ks.map (fun k => restoringSeamCost w W N s
      (coreStart width k)
      (coreLength s width k))).sum ≤
      ks.length*(250*(N+1)*(s*W)) := by
    induction ks with
    | nil => simp
    | cons k ks ih =>
      have hk := restoringSeamCost_le w W N s
        (coreStart width k)
        (coreLength s width k) hs hW hw
        (hstart k (by simp)) (by
          unfold coreLength
          omega)
      have ht := ih (by simp only [List.length_cons] at hcount; omega)
        (fun j hj => hstart j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have hm := Nat.mul_le_mul_right (250*(N+1)*(s*W)) hcount
  nlinarith

/-- Charge the physical archive order returned by the shared boundary crop run. -/
theorem boundaryRestoringSeamCost_le (w W N s width : ℕ)
    (hs : 1 ≤ s) (hW : 1 ≤ W) (hw : w ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) :
    ((boundaryCropSchedule s width).reverse.map (fun k =>
      restoringSeamCost w W N s (coreStart width k) (coreLength s width k))).sum ≤
      750*(N+1)*(s*W) := by
  have hspec := boundaryCropSchedule_spec s width hwidth hroom
  apply restoringSeamCost_sum_le w W N s width _ hs hW hw
  · simp [hspec.1]
  · intro k hk
    exact (hspec.2.2 k (List.mem_reverse.mp hk)).2.1.le

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
