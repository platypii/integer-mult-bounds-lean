import IntegerMultBounds.Networks.BinaryWalsh

/-! Complex conjugation converts the literal forward translation-kernel list
to its inverse-phase list in the same order. This is a mathematical bridge;
physical conjugation and inverse-oriented recursive execution remain separate. -/
namespace IntegerMultBounds.Networks.BinaryWalshComplexConjugation
noncomputable section
open BinaryPhase BinaryWalsh

def conjugate {h : ℕ} (f : Arrays h) : Arrays h := fun x => star (f x)

@[simp] theorem conjugate_twice {h : ℕ} (f : Arrays h) : conjugate (conjugate f)=f := by
  funext x
  exact star_star _

theorem phase_conjugate (q : ZMod 4) : star (phase q)=phase (-q) := by
  fin_cases q
  · change star (Complex.I^0)=Complex.I^0
    simp
  · change star (Complex.I^1)=Complex.I^3
    simp [pow_succ,Complex.I_mul_I]
  · change star (Complex.I^2)=Complex.I^2
    simp [pow_succ,Complex.I_mul_I]
  · change star (Complex.I^3)=Complex.I^1
    simp [pow_succ,Complex.I_mul_I]

@[simp] theorem sign_conjugate (b : ZMod 2) : star (sign b)=sign b := by
  unfold sign
  split <;> simp

@[simp] theorem chi_conjugate {h : ℕ} (v x : Address h) : star (chi v x)=chi v x := by
  simp [chi]

@[simp] theorem volume_conjugate (h : ℕ) : star (volume h)=volume h := by
  simp [volume]

theorem walsh_conjugate {h : ℕ} (f : Arrays h) :
    conjugate (walsh h f)=walsh h (conjugate f) := by
  funext x
  simp [conjugate, walsh_apply, star_sum]

theorem inverse_walsh_conjugate {h : ℕ} (f : Arrays h) :
    conjugate ((walshEquiv h).symm f)=(walshEquiv h).symm (conjugate f) := by
  change conjugate ((volume h)⁻¹ • walsh h f)=
    (volume h)⁻¹ • walsh h (conjugate f)
  rw [← walsh_conjugate]
  funext x
  simp [conjugate, Pi.smul_apply, smul_eq_mul]

theorem diagonal_conjugate {h : ℕ} (q : Address h → ZMod 4) (f : Arrays h) :
    conjugate (phaseDiagonal q f)=phaseDiagonal (fun x => -q x) (conjugate f) := by
  funext x
  change star (phase (q x) * f x)=phase (-q x) * star (f x)
  rw [star_mul, phase_conjugate]
  exact mul_comm _ _

theorem frame_conjugate {h : ℕ} (q : Address h → ZMod 4) (f : Arrays h) :
    conjugate (frame q f)=frame (fun x => -q x) (conjugate f) := by
  simp only [frame_apply,walsh_conjugate,diagonal_conjugate,inverse_walsh_conjugate]

theorem kernel_conjugate {h : ℕ} (q : ZMod 4) (v : Address h) (f : Arrays h) :
    conjugate (kernel q v f)=kernel (-q) v (conjugate f) := by
  funext x
  simp only [conjugate,kernel_apply,star_add,star_mul,star_div₀,phase_conjugate,
    star_sub,star_one,star_ofNat]
  ring

theorem run_conjugate {h : ℕ} (gs : List (ZMod 4 × Address h)) (f : Arrays h) :
    conjugate (kernelRun gs f)=kernelRun (negateKernels gs) (conjugate f) := by
  induction gs generalizing f with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨q,v⟩
    simpa only [kernelRun,negateKernels,List.map_cons,kernel_conjugate] using ih (kernel q v f)

theorem inverse_phase_run {h : ℕ} (gs : List (ZMod 4 × Address h)) (f : Arrays h) :
    kernelRun (negateKernels gs) f=conjugate (kernelRun gs (conjugate f)) := by
  rw [run_conjugate,conjugate_twice]

end
end IntegerMultBounds.Networks.BinaryWalshComplexConjugation
