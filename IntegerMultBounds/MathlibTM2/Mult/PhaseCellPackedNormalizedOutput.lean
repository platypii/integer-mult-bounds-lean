module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundDimensions

/-! Packed normalized publication certificates, independent of factory execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The ordinary published word carries the generated-window accuracy certificate. -/
def PackedNormalizedOutput {A s : ℕ} [NeZero s] (p W targetOut coreWidth k localityTarget : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (word : List (Fin (A+4))) : Prop :=
  let j := inverseNormalizationShift p
  ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Fs.length ∧
    word = (Gs.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten ∧
    List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
      (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k D)))
      (fun i => ((2 : ℂ)^j)⁻¹*componentSolution Y F i)
      ((2/(2 : ℝ)^p+(1/(2 : ℝ)^targetOut)/(2 : ℝ)^j)+
        (1/(2 : ℝ)^localityTarget+1/(2 : ℝ)^localityTarget)/(2 : ℝ)^j)) Fs Gs

/-- Publication volume depends only on the replica count, owned core and word width. -/
theorem PackedNormalizedOutput.length {A s p W targetOut coreWidth k localityTarget : ℕ}
    [NeZero s] {Fs : List (ZMod s → GaussianInt)}
    {Y : (ZMod s → GaussianInt) → ZMod s → ℝ} {word : List (Fin (A+4))}
    (h : PackedNormalizedOutput p W targetOut coreWidth k localityTarget Fs Y word) :
    word.length = Fs.length * coreLength s coreWidth k * W := by
  obtain ⟨Gs,hGs,rfl,_⟩ := h
  simp only [List.length_flatten,List.map_map,Function.comp_def,length_cstream,ownedCoreWords_length,
    List.map_const',List.sum_replicate,hGs,nsmul_eq_mul,Nat.cast_id,Nat.mul_assoc]

/-- A core publication fits in its enclosing routed interval. -/
theorem PackedNormalizedOutput.length_le {A s p W targetOut coreWidth k localityTarget n : ℕ}
    [NeZero s] {Fs : List (ZMod s → GaussianInt)}
    {Y : (ZMod s → GaussianInt) → ZMod s → ℝ} {word : List (Fin (A+4))}
    (h : PackedNormalizedOutput p W targetOut coreWidth k localityTarget Fs Y word)
    (hn : coreLength s coreWidth k ≤ n) : word.length ≤ Fs.length*n*W := by
  rw [h.length]
  exact Nat.mul_le_mul_right W (Nat.mul_le_mul_left Fs.length hn)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
