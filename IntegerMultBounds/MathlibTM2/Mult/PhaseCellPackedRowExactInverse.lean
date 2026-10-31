module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreExactInverse

/-! Packed rows use the same half-grid RHS and normalized rounded inverse as
the full-line supplier. The existing core perturbation lemma applies directly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface IntegerMultBounds.MathlibTM2.Mult.FastB0
variable {A s : ℕ} [NeZero s]

theorem rowTarget_rounded (r : PackedNormalizedJob A s)
    (L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hL : L ∘L PhaseCellOperator.rounded s r.t r.p r.u = 1)
    (F : ZMod s → GaussianInt) (hF : F ∈ r.Fs) :
    r.rowTarget F = (((2 : ℂ)^inverseNormalizationShift r.p)⁻¹ • L)
      ((1/2 : ℂ) • fun i => value r.p (F i)) := by
  have hre : (fun i => realPartWord (F i)) ∈ complexComponentFields r.Fs :=
    List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨F,hF,rfl⟩))
  have him : (fun i => imagPartWord (F i)) ∈ complexComponentFields r.Fs :=
    List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨F,hF,rfl⟩))
  have hsolves := componentSolution_solves r.q (r.q-r.p-1) (realMatrix s r.t r.p r.u)
    Finset.univ r.Y F (r.hY _ hre) (r.hY _ him)
  have hq : r.p+1+(r.q-r.p-1) = r.q := by have := r.hpq; omega
  have hhalf (i : ZMod s) : value r.q ((2 : GaussianInt)^(r.q-r.p-1)*F i) = (1/2 : ℂ)*value r.p (F i) := by
    have hh := halfGrid_value r.p (r.q-r.p-1) (F i)
    rw [hq] at hh
    exact hh
  have hvalue := inverse_parts r.p r.u L hL ((1/2 : ℂ) • fun i => value r.p (F i))
    (fun i => (componentSolution r.Y F i).re) (fun i => (componentSolution r.Y F i).im)
    (by funext i; simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,hhalf] using hsolves.1 i (Finset.mem_univ i))
    (by funext i; simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,hhalf] using hsolves.2 i (Finset.mem_univ i))
  funext i
  change ((2 : ℂ)^inverseNormalizationShift r.p)⁻¹*componentSolution r.Y F i =
    ((2 : ℂ)^inverseNormalizationShift r.p)⁻¹*(L ((1/2 : ℂ) • fun i => value r.p (F i))) i
  rw [hvalue]

def ExactRowOutput (r : PackedNormalizedJob A s)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (rows : List (List GaussianInt)) : Prop :=
    rows.length = r.Fs.length ∧
      (∀ row ∈ rows, row.length = coreLength s r.coreWidth r.k) ∧
      List.Forall₂ (fun F row =>
        let out := packedIntervalRead r.p r.W (coreStart r.coreWidth r.k) (cstream A r.W row)
        (∀ i ∈ ownedCore s r.coreWidth r.k, ‖out i‖ ≤ 1) ∧
        ErrorOn (ownedCore s r.coreWidth r.k) out
          ((((2 : ℂ)^inverseNormalizationShift r.p)⁻¹ • J) ((1/2 : ℂ) • fun i => value r.p (F i)))
          (3/(2 : ℝ)^r.p)) r.Fs rows

theorem RowOutput.exact_inverse (r : PackedNormalizedJob A s) [NeZero r.t]
    (hp : 4 ≤ r.p) (htarget : r.p+2 ≤ r.targetOut) (hlocal : r.localityTarget = r.targetOut)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s r.t r.α = 1)
    (rows : List (List GaussianInt)) (h : r.RowOutput rows) :
    r.ExactRowOutput J rows := by
  obtain ⟨L,hJn,hLH,hdiff⟩ := rounded_inverse_endpoint r.bounds.hst r.bounds.hα r.p r.u r.bounds.hp
    r.bounds.hwidth r.bounds.hαu r.bounds.hθ r.bounds.hgap r.bounds.hbudget J hJ
  let δ := 32*(r.p : ℝ)^2/(2 : ℝ)^(45*r.p)
  have hcore : r.rowError ≤ (11/4 : ℝ)/(2 : ℝ)^r.p := by
    simpa only [rowError,hlocal] using (generatedCore_error_le_quarters (j := inverseNormalizationShift r.p) htarget)
  have htotal : r.rowError+δ/2 ≤ 3/(2 : ℝ)^r.p := by
    have he := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^r.p)).mp hcore
    have hm := gridInverse_matrix_error_le_quarter hp
    change (2 : ℝ)^r.p*(δ/2) ≤ 1/4 at hm
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^r.p)).mpr
    nlinarith only [he,hm]
  have hsmall : r.rowError+δ/2 ≤ 1/2 := htotal.trans (publishedInverse_smallness hp)
  refine ⟨h.1,h.2.1,?_⟩
  have hmembers := (List.forall₂_and_left r.Fs rows).mpr ⟨fun _ hF => hF,h.2.2⟩
  apply hmembers.imp
  intro F row hpair
  obtain ⟨hF,herror⟩ := hpair
  have hv : ‖fun i => value r.p (F i)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr (r.hF F hF)
  rw [r.rowTarget_rounded L hLH F hF] at herror
  obtain ⟨hball,htransfer⟩ := inverse_core_value_spec r.p (inverseNormalizationShift r.p) J L hJn
    (inverseNormalizationShift_large r.p) r.rowError δ (by unfold rowError; positivity) hdiff hsmall
    (ownedCore s r.coreWidth r.k) (fun i => value r.p (F i)) _ hv herror
  exact ⟨hball,fun i hi => (htransfer i hi).trans htotal⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
