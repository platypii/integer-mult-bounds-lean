import IntegerMultBounds.Machine.RecursiveAffineDimensionsClean
import IntegerMultBounds.Machine.RecursiveChildQuotientsBound
import IntegerMultBounds.Machine.RecursiveChildPrepare

/-! Fully paid within-group coordinate-view preparation. A fixed program starts
with only the original six headers, initializes its divisors, computes width
and row quotients, constructs all spectator powers/products, replaces occupied
headers and erases every temporary copy. Parent-header restoration is separate. -/
namespace IntegerMultBounds.Machine.RecursiveAffinePrepare
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveAffineDimensions (Group)
open RecursiveAffineDimensionsClean (headers view)
variable {q : ℕ}
noncomputable section

theorem volume_positive (hq : 2 ≤ q) (v : Descriptor) (hp : v.Positive) : 0 < volume q v := by
  have hq' : 0 < q := by omega
  rcases hp with ⟨hA,hR,hB,hC,hE⟩
  unfold volume
  positivity

theorem header_log (hq : 2 ≤ q) (v : Descriptor) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) (z : Fin 6) :
    (hs z).length ≤ Nat.log2 (volume q v)+1 := by
  have hh := GrowingCounterData.canonical_width (hs z) (hv.2 z)
  rw [hv.1 z] at hh
  have hl : Nat.log2 (RecursiveDimensionBank.values v z) ≤ Nat.log2 (volume q v) := by
    by_cases hz : RecursiveDimensionBank.values v z = 0
    · simp [hz]
    · exact (Nat.le_log2 (Nat.ne_of_gt (volume_positive hq v hp))).mpr
        ((Nat.log2_self_le hz).trans (RecursiveHeaderBounds.values_le_volume hq v hp z))
  exact hh.trans (Nat.add_le_add_right hl 1)

def quotientConstant (m : ℕ) : ℕ :=
  6309+389*((RecursiveChildQuotientsConstant.bits m).length+(RecursiveChildQuotientsConstant.bits 1).length)

theorem quotient_cost (hq : 2 ≤ q) (v : Descriptor) (hp : v.Positive) (m : ℕ)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) :
    RecursiveChildQuotients.cost m 1 hs ≤ quotientConstant m*volume q v := by
  have hV := volume_positive hq v hp
  have hb := RecursiveChildQuotientsBound.fixed_divisor_cost (hs 3) (RecursiveChildQuotientsConstant.bits m)
    1 (volume q v) hV (by simpa only [one_mul] using header_log hq v hp hs hv 3)
  have hr := RecursiveChildQuotientsBound.fixed_divisor_cost (hs 1) (RecursiveChildQuotientsConstant.bits 1)
    1 (volume q v) hV (by simpa only [one_mul] using header_log hq v hp hs hv 1)
  have ho := Nat.le_mul_of_pos_right
    (5*((RecursiveChildQuotientsConstant.bits m).length+(RecursiveChildQuotientsConstant.bits 1).length)+25) hV
  unfold RecursiveChildQuotients.cost quotientConstant
  nlinarith

private theorem handoff_output (hq : 2 ≤ q) (b : ℕ) (v : Descriptor)
    (hs : Fin 6 → List Bool) (bs rs : List Bool) {m : ℕ} (j i : Fin m) (g : Group) :
    RecursiveChildHeaderHandoff.output (headers hq b v hs bs rs j i g)
      (RecursiveAffineDimensionsClean.output hq b v hs bs rs j i g) =
        RecursiveChildHeaderHandoff.canonical (headers hq b v hs bs rs j i g) := by
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl

private theorem handoff_hoare (hq : 2 ≤ q) (b : ℕ) (v : Descriptor)
    (hs : Fin 6 → List Bool) (bs rs : List Bool) {m : ℕ} (j i : Fin m) (g : Group) :
    HoareTime (RecursiveChildHeaderHandoff.program q)
      (fun w => w = RecursiveAffineDimensionsClean.output hq b v hs bs rs j i g)
      (fun w => w = RecursiveChildHeaderHandoff.canonical (headers hq b v hs bs rs j i g))
      (RecursiveChildHeaderHandoff.cost hs (headers hq b v hs bs rs j i g)) := by
  have hh := RecursiveChildHeaderHandoff.hands_off hs (headers hq b v hs bs rs j i g)
    (RecursiveAffineDimensionsClean.output hq b v hs bs rs j i g)
    (by intro z; fin_cases z <;> exact ⟨rfl,rfl⟩)
    (by intro z; fin_cases z <;> exact ⟨rfl,rfl⟩)
  simpa only [handoff_output] using hh

def program (hq : 2 ≤ q) {m : ℕ} (j i : Fin m) (g : Group) :=
  seq (seq (RecursiveChildQuotients.program (a := q) m 1)
    (RecursiveAffineDimensionsClean.program hq j i g)) (RecursiveChildHeaderHandoff.program q)

def constant (m : ℕ) := quotientConstant m+97*(96*m+512)+11900

/-- No quotient or generated descriptor is assumed. The final whole bank has
only six canonical view headers and blank zero-head work tapes. -/
theorem prepares (hq : 2 ≤ q) (b : ℕ) (v : Descriptor) {m : ℕ} (j i : Fin m) (g : Group)
    (hji : j < i) (hw : v.width=m*b) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (view (q := q) b v j i g) ch ∧
      HoareTime (program hq j i g)
        (fun w => w = RecursiveChildHeaderHandoff.canonical hs)
        (fun w => w = RecursiveChildHeaderHandoff.canonical ch) (constant m*volume q v) := by
  have hm : 0 < m := by have hi := i.isLt; omega
  obtain ⟨bs,rs,cb,cr,hb,hr,hquot⟩ := RecursiveChildQuotients.quotients_hoare (a := q) m 1 hm (by decide) hs
  have hb' : Counter.value bs = b := by
    rw [show Counter.value (hs 3) = v.width from hv.1 3,hw,Nat.mul_div_right b hm] at hb
    exact hb
  have hr' : Counter.value rs = v.rows := by
    rw [show Counter.value (hs 1) = v.rows from hv.1 1,Nat.div_one] at hr
    exact hr
  let ch := headers hq b v hs bs rs j i g
  have hch : RecursiveDimensionBank.Headers (view (q := q) b v j i g) ch :=
    RecursiveAffineDimensionsClean.headers_spec hq b v hs bs rs j i g hv hb' cb hr' cr
  have hview : (view (q := q) b v j i g).Positive := by
    cases g
    · exact RecursiveAffineViews.withinH_positive q b (by omega) v hp j i
    · exact RecursiveAffineViews.withinD_positive q b (by omega) v hp j i
  have hvol : volume q (view (q := q) b v j i g) = volume q v := by
    cases g
    · exact RecursiveAffineViews.withinH_volume q b v j i hji hw
    · exact RecursiveAffineViews.withinD_volume q b v j i hji hw
  have hV := volume_positive hq v hp
  have hold (z : Fin 6) : (hs z).length ≤ 2*volume q v := by
    have hh := header_log hq v hp hs hv z
    have hl := Nat.log2_le_self (volume q v)
    omega
  have hnew (z : Fin 6) : (ch z).length ≤ 2*volume q v := by
    have hh := header_log hq _ hview ch hch z
    rw [hvol] at hh
    have hl := Nat.log2_le_self (volume q v)
    omega
  have hh := (hquot.seq (RecursiveAffineDimensionsClean.constructs_hoare hq b v hs bs rs j i g hji hw hv hp hb' cb)).seq
    (handoff_hoare hq b v hs bs rs j i g)
  rw [RecursiveChildPrepare.input_eq] at hh
  refine ⟨ch,hch,hh.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  have hqc := quotient_cost hq v hp m hs hv
  have hhc := RecursiveChildHeaderHandoff.cost_le hs ch (2*volume q v) hold hnew
  unfold constant
  change RecursiveChildQuotients.cost m 1 hs+1+(97*(96*m+512)*volume q v+11756)+1+
    RecursiveChildHeaderHandoff.cost hs ch ≤ _
  nlinarith

end
end IntegerMultBounds.Machine.RecursiveAffinePrepare
