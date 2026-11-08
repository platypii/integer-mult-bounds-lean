module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoverySolutions
public import IntegerMultBounds.NLogN.PhaseCellLocality
public import IntegerMultBounds.NLogN.PhaseCellTargetCoreLocality
public import IntegerMultBounds.NLogN.ToeplitzLocal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface

/-! Construct the ambient half-grid target and compare the owned principal solutions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryAxisBounds
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
variable {s t p u l : ℕ} [NeZero s] {alpha gap : ℝ}

noncomputable def globalRealSolver (h : RecoveryAxisBounds s t p u l alpha gap) :
    (ZMod s → ℝ) → ZMod s → ℝ :=
  Classical.choose (exists_solver (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ)))
    (by have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := h.hp; omega)
        positivity) h.hdom)

theorem globalRealSolver_solves (h : RecoveryAxisBounds s t p u l alpha gap) (rhs : ZMod s → ℝ) :
    Solves (realMatrix s t p u) Finset.univ (h.globalRealSolver rhs) rhs :=
  Classical.choose_spec (exists_solver (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ)))
    (by have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := h.hp; omega)
        positivity) h.hdom) rhs

noncomputable def globalHalfGridTarget (h : RecoveryAxisBounds s t p u l alpha gap)
    (F : ZMod t → GaussianInt) (i : ZMod s) : ℂ :=
  ⟨h.globalRealSolver (fun j => ((1/2 : ℂ)*value p (F (rowIndex s t j))).re) i,
   h.globalRealSolver (fun j => ((1/2 : ℂ)*value p (F (rowIndex s t j))).im) i⟩

theorem globalHalfGridTarget_solves (h : RecoveryAxisBounds s t p u l alpha gap) (F : ZMod t → GaussianInt) :
    Solves (realMatrix s t p u) Finset.univ (fun i => (h.globalHalfGridTarget F i).re)
      (fun i => ((1/2 : ℂ)*value p (F (rowIndex s t i))).re) ∧
    Solves (realMatrix s t p u) Finset.univ (fun i => (h.globalHalfGridTarget F i).im)
      (fun i => ((1/2 : ℂ)*value p (F (rowIndex s t i))).im) :=
  ⟨h.globalRealSolver_solves _,h.globalRealSolver_solves _⟩

theorem ownedTargets_global_error (h : RecoveryAxisBounds s t p u l alpha gap) (target L k : ℕ)
    (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    List.Forall₂ (fun F z => ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
      z (h.globalHalfGridTarget F) (2/(2 : ℝ)^target)) Fs (h.ownedTargets target L k hnear hL ha hb hfit Fs) := by
  have hsolves := h.ownedTargets_solves target L k hnear hL ha hb hfit Fs hF
  have hm := (List.forall₂_and_left Fs (h.ownedTargets target L k hnear hL ha hb hfit Fs)).mpr
    ⟨fun F hmem => hmem,hsolves⟩
  apply List.Forall₂.imp _ hm
  intro F z hpair
  have hglobal := h.globalHalfGridTarget_solves F
  have hlocal (x y rhs : ZMod s → ℝ)
      (hx : Solves (realMatrix s t p u) Finset.univ x rhs)
      (hy : Solves (realMatrix s t p u)
        (haloVertices s (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
          (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)) y rhs)
      (hrhs : ∀ i, |rhs i| ≤ 1) (i : ZMod s)
      (hi : i ∈ haloVertices s (cut s t L k) (cut s t L (k+1))) : |y i-x i| ≤ 1/(2 : ℝ)^target := by
    apply halo_locality_precision h.hst h.hα p u target h.hp h.hpacket h.hαu h.hθ h.hgap h.hbudget
      _ _ hb x y rhs hx hy hrhs i
    rw [owned_haloLayer t L k _ _ ha]
    exact hi
  have hrhs (i : ZMod s) : ‖(1/2 : ℂ)*value p (F (rowIndex s t i))‖ ≤ 1 := by
    rw [norm_mul]
    have hh := hF F hpair.1 (rowIndex s t i)
    norm_num
    linarith
  intro i hi
  have hre := hlocal _ _ _ hglobal.1 hpair.2.1
    (fun j => (Complex.abs_re_le_norm _).trans (hrhs j)) i hi
  have him := hlocal _ _ _ hglobal.2 hpair.2.2
    (fun j => (Complex.abs_im_le_norm _).trans (hrhs j)) i hi
  have hn := Complex.norm_le_abs_re_add_abs_im (z i-h.globalHalfGridTarget F i)
  simp only [Complex.sub_re,Complex.sub_im] at hn
  have hh := hn.trans (add_le_add hre him)
  convert hh using 1
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryAxisBounds
