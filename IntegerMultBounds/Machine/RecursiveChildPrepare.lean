import IntegerMultBounds.Machine.RecursiveChildQuotientsBound
import IntegerMultBounds.Machine.RecursiveChildHeaderHandoff

/-! Complete physical preparation of one recursive child header bank. Fixed
constants, divisions, powers, products, old-header replacement, temporary-copy
erasure and all joins are charged. Parent headers must first be saved by the
caller; the machine leaves only the canonical six child headers. -/
namespace IntegerMultBounds.Machine.RecursiveChildPrepare
open RecursiveInterchangeLayout RecursiveInterchangeVolume
variable {q : ℕ}
noncomputable section

def program (hq : 2 ≤ q) (roles : ℕ) {m : ℕ} (i j : Fin m) :=
  seq (RecursiveChildQuotients.program (a := q) m roles)
    (RecursiveChildHeaderHandoff.constructProgram hq i j)

theorem input_eq (hs : Fin 6 → List Bool) :
    RecursiveChildQuotients.input (a := q) hs = RecursiveChildHeaderHandoff.canonical hs := by
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded _

def constant (m roles : ℕ) := RecursiveChildQuotientsBound.constant m roles+
  97*(48*(m-1)+512)+60*(Nat.log2 roles+2)+11840

/-- One fixed machine takes only the parent's original six canonical headers
and produces only the actual child's six canonical headers. -/
theorem prepares {roles m n k : ℕ} {root parent : Descriptor}
    (path : Path q roles m root n parent) (hq : 2 ≤ q) (hr : 0 < roles)
    (hm : 2 ≤ m) (hwroot : root.width = m^k) (hvroot : root.Positive)
    (b : ℕ) (i j : Fin m) (hw : parent.width = m*b) (hdiv : roles ∣ parent.rows)
    (hs : Fin 6 → List Bool) (hh : RecursiveDimensionBank.Headers parent hs) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (child q roles b parent i j) ch ∧
      HoareTime (program hq roles i j)
        (fun w => w = RecursiveChildHeaderHandoff.canonical hs)
        (fun w => w = RecursiveChildHeaderHandoff.canonical ch)
        (constant m roles*volume q (child q roles b parent i j)) := by
  let current := path.descend b i j hw hdiv
  have hparent := path.positive (by omega) hr hvroot
  obtain ⟨bs,rs,hbc,hrc,hbv,hrv,hquot⟩ :=
    RecursiveChildQuotientsBound.quotients_hoare_linear (a := q) current path hq hr hm hwroot hvroot hs hh
  have hb : Counter.value bs = b := by
    rw [hbv,hw,Nat.mul_div_right b (by omega : 0 < m)]
  let ch := RecursiveChildDimensions.childHeaders (q := q) parent hs bs rs b i j
  have hch : RecursiveDimensionBank.Headers (child q roles b parent i j) ch :=
    RecursiveChildDimensions.child_headers roles b parent hs bs rs i j hh hb hbc hrv hrc
  have hconstruct := RecursiveChildHeaderHandoff.constructs_hoare hq roles b parent hs bs rs i j hh hparent hb hbc hr hdiv
  have hcost := RecursiveChildHeaderHandoff.cost_le hs ch
    (2*(Nat.log2 roles+2)*volume q (child q roles b parent i j))
    (RecursiveHeaderBounds.saved_header_length_le current path hq hr hm hwroot hvroot hs hh)
    (RecursiveHeaderBounds.header_length_le current hq hr hm hwroot hvroot ch hch)
  have hV : 0 < volume q (child q roles b parent i j) :=
    lt_of_lt_of_le (pow_pos (by omega : 0 < q) _) (current.original_chunks (by omega) hr hvroot)
  refine ⟨ch,hch,?_⟩
  have h := hquot.seq hconstruct
  rw [input_eq] at h
  apply h.consequence (fun _ h => h) (fun _ h => h)
  change RecursiveChildHeaderHandoff.cost hs ch ≤ _ at hcost
  unfold constant
  nlinarith

end
end IntegerMultBounds.Machine.RecursiveChildPrepare
