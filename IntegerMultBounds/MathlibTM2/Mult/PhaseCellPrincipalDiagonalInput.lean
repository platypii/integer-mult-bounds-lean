module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedIntervalDiagonal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedRecoveryMagnitude

/-! Principal stability supplies the diagonal input radius directly from the
executed solve certificate, independently of the chosen crop and replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem componentSolution_normalized_bound {s : ℕ} (p q : ℕ) (hp : 0 < p) (hpq : p+1 ≤ q)
    (M : Matrix (ZMod s) (ZMod s) ℝ) (principal : Finset (ZMod s))
    (hdom : SchurDominance.DominatesOn M principal (1/(8*(p : ℝ))))
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves M principal (y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re)) :
    ∀ F ∈ Fs, ∀ i ∈ principal,
      ‖((2 : ℂ)^inverseNormalizationShift p)⁻¹*componentSolution y F i‖ ≤ (3/2 : ℝ) := by
  intro F hmem i hi
  have hre : (fun i => realPartWord (F i)) ∈ complexComponentFields Fs :=
    List.mem_append_left _ (List.mem_map.mpr ⟨F,hmem,rfl⟩)
  have him : (fun i => imagPartWord (F i)) ∈ complexComponentFields Fs :=
    List.mem_append_right _ (List.mem_map.mpr ⟨F,hmem,rfl⟩)
  have hs := componentSolution_solves q (q-p-1) M principal y F (hy _ hre) (hy _ him)
  have hq : p+1+(q-p-1) = q := by omega
  have hhalf (j : ZMod s) : value q ((2 : GaussianInt)^(q-p-1)*F j) =
      (1/2 : ℂ)*value p (F j) := by
    have hh := halfGrid_value p (q-p-1) (F j)
    rw [hq] at hh
    exact hh
  simp_rw [hhalf] at hs
  have hbound := halfGridSolution_norm_le p hp M principal hdom
    (fun j => value p (F j)) (componentSolution y F) (hF F hmem) hs.1 hs.2 i hi
  have hj := inverseNormalizationShift_large p
  have hpos : (0 : ℝ) < (2 : ℝ)^inverseNormalizationShift p := by positivity
  rw [norm_mul,norm_inv,norm_pow,Complex.norm_ofNat,inv_mul_eq_div]
  apply (div_le_iff₀ hpos).mpr
  nlinarith

theorem PackedPrincipalOutput.diagonal_targets {A s p q W target start rows : ℕ} [NeZero s]
    {M : Matrix (ZMod s) (ZMod s) ℝ} {principal : Finset (ZMod s)}
    {Fs : List (ZMod s → GaussianInt)} {word : List (Fin (A+4))}
    (h : PackedPrincipalOutput M principal p q W target start rows Fs word)
    (hp : 0 < p) (hpq : p+1 ≤ q)
    (hdom : SchurDominance.DominatesOn M Finset.univ (1/(8*(p : ℝ))))
    (hcore : haloVertices s start (start+rows) ⊆ principal)
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    ∃ y : (ZMod s → GaussianInt) → ZMod s → ℝ,
      (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves M principal (y F)
        (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re)) ∧
      PackedIntervalOutput p W start rows
        (Fs.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*componentSolution y F i))
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p) word ∧
      ∀ z ∈ Fs.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*componentSolution y F i),
        ∀ i ∈ haloVertices s start (start+rows), ‖z i‖ ≤ (3/2 : ℝ) := by
  obtain ⟨y,hy,hpacket⟩ := h
  refine ⟨y,hy,hpacket,?_⟩
  intro z hz i hi
  obtain ⟨F,hmem,rfl⟩ := List.mem_map.mp hz
  exact componentSolution_normalized_bound p q hp hpq M principal
    (SchurDominance.dominates_mono M Finset.univ principal _ (Finset.subset_univ _) hdom)
    Fs hF y hy F hmem i (hcore hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
