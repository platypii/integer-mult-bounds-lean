module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedFactoryDescriptorStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreExactInverse
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandStreams

/-! Convert actual cyclic bulk output to the same exact-inverse row contract
as seam crops, reusing component uniqueness and the existing perturbation bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry PhaseCellInterface
  IntegerMultBounds.MathlibTM2.Mult.FastB0
variable {A s : ℕ} [NeZero s]

theorem componentSolution_rounded {p q u t : ℕ} (hpq : p+1 ≤ q)
    (Fs : List (ZMod s → GaussianInt)) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hL : L ∘L PhaseCellOperator.rounded s t p u = 1)
    (F : ZMod s → GaussianInt) (hF : F ∈ Fs) :
    componentSolution Y F = L ((1/2 : ℂ) • fun i => value p (F i)) := by
  have hre : (fun i => realPartWord (F i)) ∈ complexComponentFields Fs :=
    List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨F,hF,rfl⟩))
  have him : (fun i => imagPartWord (F i)) ∈ complexComponentFields Fs :=
    List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨F,hF,rfl⟩))
  have hsolves := componentSolution_solves q (q-p-1) (realMatrix s t p u)
    Finset.univ Y F (hY _ hre) (hY _ him)
  have hq : p+1+(q-p-1) = q := by omega
  have hhalf (i : ZMod s) : value q ((2 : GaussianInt)^(q-p-1)*F i) = (1/2 : ℂ)*value p (F i) := by
    have hh := halfGrid_value p (q-p-1) (F i)
    rw [hq] at hh
    exact hh
  have hvalue := inverse_parts p u L hL ((1/2 : ℂ) • fun i => value p (F i))
    (fun i => (componentSolution Y F i).re) (fun i => (componentSolution Y F i).im)
    (by funext i; simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,hhalf] using hsolves.1 i (Finset.mem_univ i))
    (by funext i; simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,hhalf] using hsolves.2 i (Finset.mem_univ i))
  simpa only [Complex.eta] using hvalue.symm

theorem PackedNormalizedOutput.exact_rows {p W target width k q t u l : ℕ} [NeZero t] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (hp : 4 ≤ p) (htarget : p+2 ≤ target) (hpq : p+1 ≤ q)
    (Fs : List (ZMod s → GaussianInt)) (hFs : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1)
    {word : List (Fin (A+4))} (h : PackedNormalizedOutput p W target width k target Fs Y word) :
    ∃ rows, word = cstream A W rows.flatten ∧ ExactCoreRows (A := A) p W width k Fs J rows := by
  obtain ⟨L,hJn,hLH,hdiff⟩ := rounded_inverse_endpoint axis.hst axis.hα p u axis.hp
    axis.hpacket axis.hαu axis.hθ axis.hgap axis.hbudget J hJ
  let j := inverseNormalizationShift p
  let error := (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j)+
    (1/(2 : ℝ)^target+1/(2 : ℝ)^target)/(2 : ℝ)^j
  let δ := 32*(p : ℝ)^2/(2 : ℝ)^(45*p)
  have hcore : error ≤ (11/4 : ℝ)/(2 : ℝ)^p := generatedCore_error_le_quarters htarget
  have htotal : error+δ/2 ≤ 3/(2 : ℝ)^p := by
    have he := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^p)).mp hcore
    have hm := gridInverse_matrix_error_le_quarter hp
    change (2 : ℝ)^p*(δ/2) ≤ 1/4 at hm
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^p)).mpr
    nlinarith only [he,hm]
  have hsmall : error+δ/2 ≤ 1/2 := htotal.trans (publishedInverse_smallness hp)
  obtain ⟨Gs,hcount,hword,hgood⟩ := h
  let rows := Gs.map (ownedCoreWords width k)
  have hbytes : cstream A W rows.flatten = (Gs.map (fun D => cstream A W (ownedCoreWords width k D))).flatten := by
    simpa only [List.flatMap] using cstream_flatMap_rows (A := A) (w := W) Gs (ownedCoreWords width k)
  refine ⟨rows,hword.trans hbytes.symm,?_,?_,?_⟩
  · simpa only [rows,List.length_map] using hcount
  · intro row hr
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hr
    exact ownedCoreWords_length width k D
  · apply List.forall₂_map_right_iff.mpr
    have hmembers := (List.forall₂_and_left Fs Gs).mpr ⟨fun _ hF => hF,hgood⟩
    apply hmembers.imp
    intro F D hpair
    obtain ⟨hF,herror⟩ := hpair
    have htargetEq := componentSolution_rounded hpq Fs Y hY L hLH F hF
    have hv : ‖fun i => value p (F i)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr (hFs F hF)
    rw [htargetEq] at herror
    obtain ⟨hball,htransfer⟩ := inverse_core_value_spec p j J L hJn (inverseNormalizationShift_large p)
      error δ (by dsimp only [error]; positivity) hdiff hsmall (ownedCore s width k)
      (fun i => value p (F i)) _ hv herror
    exact ⟨hball,fun i hi => (htransfer i hi).trans htotal⟩

theorem packedNormalizedOutputs_exact_rows {p W target width q t u l : ℕ} [NeZero t] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (hp : 4 ≤ p) (htarget : p+2 ≤ target) (hpq : p+1 ≤ q)
    (Fs : List (ZMod s → GaussianInt)) (hFs : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1)
    {ks : List ℕ} {outputs : List (List (Fin (A+4)))}
    (h : List.Forall₂ (fun k word => PackedNormalizedOutput p W target width k target Fs Y word) ks outputs) :
    ∃ batches, outputs = batches.map (fun rows => cstream A W rows.flatten) ∧
      List.Forall₂ (fun k rows => ExactCoreRows (A := A) p W width k Fs J rows) ks batches := by
  induction h with
  | nil => exact ⟨[],rfl,.nil⟩
  | @cons k word ks outputs hhead htail ih =>
    obtain ⟨rows,hword,hrows⟩ := hhead.exact_rows axis hp htarget hpq Fs hFs Y hY J hJ
    obtain ⟨batches,houtputs,hbatches⟩ := ih
    exact ⟨rows::batches,by simp only [List.map_cons,hword,houtputs],.cons hrows hbatches⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
