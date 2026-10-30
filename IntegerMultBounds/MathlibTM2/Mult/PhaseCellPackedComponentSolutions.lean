module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexFields
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComplexBatchAssembly
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputValue
public import IntegerMultBounds.NLogN.SchurSolve

/-! The actual real batch's component order determines its complex target and output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN

def componentSolution {s : ℕ} (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (F : ZMod s → GaussianInt) (i : ZMod s) : ℂ :=
  ⟨y (fun j => realPartWord (F j)) i,y (fun j => imagPartWord (F j)) i⟩

/-- Real and imaginary replicas use the same scalar solution map and retain
the original field order. No target permutation witness is required. -/
theorem componentSolution_targets {s : ℕ} (Fs : List (ZMod s → GaussianInt))
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ) :
    complexComponentTargets (Fs.map (componentSolution y)) = (complexComponentFields Fs).map y := by
  simp [complexComponentTargets,complexComponentFields,componentSolution,List.map_map,Function.comp_def]

theorem componentSolution_norm_le {s : ℕ} (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (F : ZMod s → GaussianInt) (i : ZMod s) (K : ℝ)
    (hreal : |y (fun j => realPartWord (F j)) i| ≤ K)
    (himag : |y (fun j => imagPartWord (F j)) i| ≤ K) : ‖componentSolution y F i‖ ≤ 2*K := by
  calc
    _ ≤ |y (fun j => realPartWord (F j)) i|+|y (fun j => imagPartWord (F j)) i| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2*K := by linarith

/-- The extra real-component target bit pays complex assembly exactly once. -/
theorem component_error_bit (target : ℕ) :
    (1/(2 : ℝ)^(target+1)+1/(2 : ℝ)^(target+1)) = 1/(2 : ℝ)^target := by
  rw [pow_succ]
  field_simp
  ring

/-- The constructed target solves the original shifted complex RHS component
by component on the same active vertices and the same ambient matrix. -/
theorem componentSolution_solves {s : ℕ} (q d : ℕ) (M : Matrix (ZMod s) (ZMod s) ℝ)
    (active : Finset (ZMod s)) (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (F : ZMod s → GaussianInt)
    (hre : SchurDominance.Solves M active (y (fun i => realPartWord (F i)))
      (fun i => (value q ((2 : GaussianInt)^d*realPartWord (F i))).re))
    (him : SchurDominance.Solves M active (y (fun i => imagPartWord (F i)))
      (fun i => (value q ((2 : GaussianInt)^d*imagPartWord (F i))).re)) :
    SchurDominance.Solves M active (fun i => (componentSolution y F i).re)
      (fun i => (value q ((2 : GaussianInt)^d*F i)).re) ∧
    SchurDominance.Solves M active (fun i => (componentSolution y F i).im)
      (fun i => (value q ((2 : GaussianInt)^d*F i)).im) := by
  have hpow : (2 : ℂ)^d = Complex.ofReal ((2 : ℝ)^d) := by norm_cast
  have hrhs i : (value q ((2 : GaussianInt)^d*realPartWord (F i))).re =
      (value q ((2 : GaussianInt)^d*F i)).re := by
    simp only [value_pow_two_mul,hpow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,value_realPartWord_re]
  have hihs i : (value q ((2 : GaussianInt)^d*imagPartWord (F i))).re =
      (value q ((2 : GaussianInt)^d*F i)).im := by
    simp only [value_pow_two_mul,hpow,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_zero,value_imagPartWord_re]
  constructor
  · intro i hi
    simpa only [componentSolution,hrhs] using hre i hi
  · intro i hi
    simpa only [componentSolution,hihs] using him i hi

/-- Consume the real supplier's exact shifted-input/scalar-target certificate.
The shifted RHS need not be supplied again to the assembly caller. -/
theorem packedComponentSolutions_certificate {A s : ℕ} (q w d a L : ℕ)
    (active : Finset (ZMod s)) (Fs : List (ZMod s → GaussianInt))
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ) (Ds : List (ZMod s → GaussianInt))
    (e : ℝ) (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun (x : (ZMod s → GaussianInt) × (ZMod s → ℝ)) D =>
      PhaseCellInterface.ErrorOn active
        (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail) i).re) x.2 e)
      ((complexComponentFields Fs).map (fun F => ((fun i => (2 : GaussianInt)^d*F i),y F))) Ds) :
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail) i).re) z e)
      (complexComponentTargets (Fs.map (componentSolution y))) Ds := by
  rw [componentSolution_targets]
  simpa only [List.forall₂_map_left_iff] using hgood

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Pair the actual numerical output list using its native certificate. Both
component splitting and complex target order are derived from the original Fs. -/
theorem assemblePackedComponentSolutions_exec {replicas width count src buf saved tmp : Fin T}
    (hreg : [replicas,width,count,src,buf,saved,tmp].Nodup) (hA : 4 ≤ A)
    {s : ℕ} [NeZero s] (q w d a L : ℕ) (active : Finset (ZMod s)) (hfit : a+L ≤ s)
    (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (Fs : List (ZMod s → GaussianInt)) (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (scalarTail tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun (x : (ZMod s → GaussianInt) × (ZMod s → ℝ)) D =>
      PhaseCellInterface.ErrorOn active
        (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L D)++scalarTail) i).re) x.2 e)
      ((complexComponentFields Fs).map (fun F => ((fun i => (2 : GaussianInt)^d*F i),y F))) Ds)
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = Fs.length) (hwidth : (S.R width).length = L*w)
    (hsrc : S.R src = (Ds.map (fun D => cstream A w (packedInterval a L D))).flatten++tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    let Gs := pairedComponentFields (Ds.take Fs.length) (Ds.drop Fs.length)
    Gs.length = Fs.length ∧
    ∃ v' n, v'.user = v.user ∧ n ≤ Fs.length*(16*(L*w)+9)+14 ∧
      Exec body (pairComplexKey replicas width count src buf saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A w (packedInterval a L D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail)) z (e+e))
        (Fs.map (componentSolution y)) Gs := by
  have hc := packedComponentSolutions_certificate q w d a L active Fs y Ds e scalarTail hgood
  simpa only [List.length_map] using packedComplexBatchAssembly_exec (body := body) hreg hA
    q w a L active hfit hactive (Fs.map (componentSolution y)) Ds e scalarTail tail hc v S
    (by simpa only [List.length_map] using hreplicas) hwidth hsrc hcount hbuf hsaved htmp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
