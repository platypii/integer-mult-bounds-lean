module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWindows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublication

/-! Transfer the actual normalized packed certificate from local to global solutions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface

/-- The two scalar locality losses combine once for the same complex target. -/
theorem componentSolution_error {s : ℕ} (core : Finset (ZMod s))
    (y Y : (ZMod s → GaussianInt) → ZMod s → ℝ) (F : ZMod s → GaussianInt) (e : ℝ)
    (hre : ErrorOn core (y (fun i => realPartWord (F i))) (Y (fun i => realPartWord (F i))) e)
    (him : ErrorOn core (y (fun i => imagPartWord (F i))) (Y (fun i => imagPartWord (F i))) e) :
    ErrorOn core (componentSolution y F) (componentSolution Y F) (e+e) := by
  intro i hi
  have hr := hre i hi
  have hm := him i hi
  simp only [Real.norm_eq_abs] at hr hm
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hr hm)

/-- Locality is scaled by the same exact normalization as the numerical target.
The returned packet list and its input ordering are unchanged. -/
theorem normalizedPackedComponents_global_accuracy {A s : ℕ} (p W c L j : ℕ)
    (core : Finset (ZMod s)) (Fs : List (ZMod s → GaussianInt))
    (y Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4))) (arithmetic locality : ℝ)
    (hlocal : ∀ F ∈ complexComponentFields Fs, ErrorOn core (y F) (Y F) locality)
    (hgood : List.Forall₂ (fun z D => ErrorOn core
      (packedIntervalRead p W c (cstream A W (packedInterval c L D)++tail)) z arithmetic)
      ((Fs.map (componentSolution y)).map (fun z i => ((2 : ℂ)^j)⁻¹*z i)) Ds) :
    List.Forall₂ (fun F D => ErrorOn core
      (packedIntervalRead p W c (cstream A W (packedInterval c L D)++tail))
      (fun i => ((2 : ℂ)^j)⁻¹*componentSolution Y F i)
      (arithmetic+(locality+locality)/(2 : ℝ)^j)) Fs Ds := by
  simp only [List.forall₂_map_left_iff] at hgood
  have hm := (List.forall₂_and_left Fs Ds).mpr ⟨fun _ hF => hF,hgood⟩
  apply List.Forall₂.imp _ hm
  intro F D hpair
  apply hpair.2.trans
  have hr := hlocal (fun i => realPartWord (F i))
    (List.mem_append_left _ (List.mem_map.mpr ⟨F,hpair.1,rfl⟩))
  have hi := hlocal (fun i => imagPartWord (F i))
    (List.mem_append_right _ (List.mem_map.mpr ⟨F,hpair.1,rfl⟩))
  have he := componentSolution_error core y Y F locality hr hi
  intro i hi
  rw [←mul_sub,norm_mul,norm_inv,norm_pow,Complex.norm_ofNat]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left (he i hi) (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2^j))

/-- Generated halos discharge locality for the exact component solutions used
by the native batch, including the full-system fallback at the periodic seam. -/
theorem normalizedPackedComponents_generated_accuracy {A s t : ℕ} [NeZero s]
    (hst : s < t) {α gap : ℝ} (hα : 0 < α)
    (width p u localityTarget k q j W : ℕ) (hp : 2 ≤ p) (hpq : p+1 ≤ q)
    (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1)) (hbudget : α^2*gap ≤ p)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields Fs, Solves (realMatrix s t p u)
      (generatedWindow s width p u localityTarget k).halo (y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (hY : ∀ F ∈ complexComponentFields Fs, Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4))) (arithmetic : ℝ)
    (hgood : List.Forall₂ (fun z D => ErrorOn (ownedCore s width k)
      (packedIntervalRead p W (coreStart width k)
        (cstream A W (ownedCoreWords width k D)++tail)) z arithmetic)
      ((Fs.map (componentSolution y)).map (fun z i => ((2 : ℂ)^j)⁻¹*z i)) Ds) :
    List.Forall₂ (fun F D => ErrorOn (ownedCore s width k)
      (packedIntervalRead p W (coreStart width k)
        (cstream A W (ownedCoreWords width k D)++tail))
      (fun i => ((2 : ℂ)^j)⁻¹*componentSolution Y F i)
      (arithmetic+(1/(2 : ℝ)^localityTarget+1/(2 : ℝ)^localityTarget)/(2 : ℝ)^j)) Fs Ds := by
  have hunit := complexComponentFields_norm_le p Fs hF
  apply normalizedPackedComponents_global_accuracy p W (coreStart width k) (coreLength s width k) j
    (ownedCore s width k) Fs y Y Ds tail arithmetic (1/(2 : ℝ)^localityTarget) ?_
    (by simpa only [ownedCoreWords,packedInterval] using hgood)
  intro F hmem
  apply generatedWindow_solution_error hst hα width p u localityTarget k hp hwidth hαu hθ hgap hbudget
    (Y F) (y F) _ (hY F hmem) (hy F hmem)
  intro i
  have hu := hunit F hmem i
  rw [(packedInputShift_value_fits p q hpq (F i) hu).1]
  calc
    _ ≤ ‖(1/2 : ℂ)*value p (F i)‖ := Complex.abs_re_le_norm _
    _ = (1/2 : ℝ)*‖value p (F i)‖ := by rw [norm_mul]; norm_num
    _ ≤ 1/2 := by linarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
