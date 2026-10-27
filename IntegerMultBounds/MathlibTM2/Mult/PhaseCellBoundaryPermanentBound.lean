module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorPrepared

/-! A uniform per-register bound for factor data that survives until release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

def boundaryTransientRoles : List RsbR := [.src,.m2wn,.kn,.tK,.sel,.vk,.dout]

def BoundaryPermanentBound {A : ℕ} (σ : RsbR → List (Fin (A+4))) (D : ℕ) : Prop :=
  ∀ r, r ∉ boundaryTransientRoles → (σ r).length ≤ D

def boundaryPermanentSizeBound (q band N : ℕ) : ℕ :=
  let w := 2*q+8
  let W := 12*band+1
  q+IntegerMultBounds.Schoenhage.Schedule.topN w+3*w+3*W+W*w+N+
    (2*W+1)*w+(W+1)*(2*W+1)*w+N*w+2*(N*W*w)

theorem BoundaryPermanentBound.update {A D : ℕ} {σ : RsbR → List (Fin (A+4))}
    (h : BoundaryPermanentBound σ D) (r : RsbR) (hr : r ∈ boundaryTransientRoles)
    (xs : List (Fin (A+4))) : BoundaryPermanentBound (Function.update σ r xs) D := by
  intro k hk
  have hkr : k ≠ r := by intro he; subst k; exact hk hr
  simpa only [Function.update_of_ne hkr] using h k hk

theorem boundaryPermanentBound_of_factor {A p q band N : ℕ}
    (σ τ : RsbR → List (Fin (A+4))) (h : BoundaryFactorPrepared σ p q band N)
    (hcm : ∀ c ∈ ([CR.xs,.ys,.out] : List CR), σ (.cm c) = [])
    (hextra : ∀ r ∈ ([RsbR.prm,.dtab,.padc] : List RsbR), σ r = [])
    (hbo : (τ .bo).length ≤ N*(12*band+1)*(2*q+8))
    (hhf : (τ .hf).length ≤ N*(12*band+1)*(2*q+8))
    (hdf : (τ .df).length ≤ N*(2*q+8))
    (hm2n : (τ .m2n).length = 12*band+1)
    (hmwn : (τ .mwn).length = (12*band+1)*(2*q+8))
    (hms : τ .ms = σ .dst) (hef : τ .ef = []) (hxs : τ .xs = [])
    (hframe : ∀ r, r ∉ ([RsbR.src,.hf,.df,.dout,.bo,.vk,.m2n,.kn,.ms,.mwn,.ef,.xs] : List RsbR) → τ r = σ r) :
    BoundaryPermanentBound τ (boundaryPermanentSizeBound q band N) := by
  intro r hr
  cases r with
  | cm c =>
    rw [hframe (.cm c) (by simp)]
    by_cases hc : c ∈ ([CR.xs,.ys,.out] : List CR)
    · rw [hcm c hc]; simp
    have hxs' : c ≠ .xs := by intro he; apply hc; simp [he]
    have hys' : c ≠ .ys := by intro he; apply hc; simp [he]
    have hout : c ≠ .out := by intro he; apply hc; simp [he]
    by_cases hwn : c = .wn
    · subst c; rw [h.ready.wn]; dsimp [boundaryPermanentSizeBound]; omega
    by_cases hpn : c = .pn
    · subst c; rw [h.ready.pn]; dsimp [boundaryPermanentSizeBound]; omega
    by_cases hnn : c = .nn
    · subst c; rw [h.ready.nn]; dsimp [boundaryPermanentSizeBound]; omega
    rw [h.ready.empty c hxs' hys' hout hwn hpn hnn]
    simp
  | src => exact False.elim (hr (by simp [boundaryTransientRoles]))
  | m2wn => exact False.elim (hr (by simp [boundaryTransientRoles]))
  | kn => exact False.elim (hr (by simp [boundaryTransientRoles]))
  | tK => exact False.elim (hr (by simp [boundaryTransientRoles]))
  | sel => exact False.elim (hr (by simp [boundaryTransientRoles]))
  | vk => exact False.elim (hr (by simp [boundaryTransientRoles]))
  | dout => exact False.elim (hr (by simp [boundaryTransientRoles]))
  | dst =>
    rw [hframe .dst (by decide),h.dst]
    dsimp [boundaryPermanentSizeBound]
    omega
  | msk =>
    rw [hframe .msk (by decide),h.mask]
    simp only [length_csyms]
    dsimp [boundaryPermanentSizeBound]
    omega
  | ms =>
    rw [hms,h.dst]
    dsimp [boundaryPermanentSizeBound]
    omega
  | mwn =>
    rw [hmwn]
    dsimp [boundaryPermanentSizeBound]
    omega
  | m2n =>
    rw [hm2n]
    dsimp [boundaryPermanentSizeBound]
    omega
  | sn =>
    rw [hframe .sn (by decide),h.sn]
    dsimp [boundaryPermanentSizeBound]
    omega
  | smwn =>
    rw [hframe .smwn (by decide),h.smwn]
    dsimp [boundaryPermanentSizeBound]
    omega
  | tswn =>
    rw [hframe .tswn (by decide),h.tswn]
    dsimp [boundaryPermanentSizeBound]
    omega
  | bx =>
    rw [hframe .bx (by decide),h.seed]
    simp only [length_csyms]
    dsimp [boundaryPermanentSizeBound]
    omega
  | bo =>
    apply hbo.trans
    dsimp [boundaryPermanentSizeBound]
    omega
  | hf =>
    apply hhf.trans
    dsimp [boundaryPermanentSizeBound]
    omega
  | df =>
    apply hdf.trans
    dsimp [boundaryPermanentSizeBound]
    omega
  | ef => rw [hef]; simp
  | xs => rw [hxs]; simp
  | tL => rw [hframe .tL (by decide),h.empty .tL (by simp [boundaryFactorScratch])]; simp
  | tJ => rw [hframe .tJ (by decide),h.empty .tJ (by simp [boundaryFactorScratch])]; simp
  | tC => rw [hframe .tC (by decide),h.empty .tC (by simp [boundaryFactorScratch])]; simp
  | tA => rw [hframe .tA (by decide),h.empty .tA (by simp [boundaryFactorScratch])]; simp
  | sr => rw [hframe .sr (by decide),h.empty .sr (by simp [boundaryFactorScratch])]; simp
  | hv => rw [hframe .hv (by decide),h.empty .hv (by simp [boundaryFactorScratch])]; simp
  | b1 => rw [hframe .b1 (by decide),h.empty .b1 (by simp [boundaryFactorScratch])]; simp
  | ya => rw [hframe .ya (by decide),h.empty .ya (by simp [boundaryFactorScratch])]; simp
  | tb => rw [hframe .tb (by decide),h.empty .tb (by simp [boundaryFactorScratch])]; simp
  | xa => rw [hframe .xa (by decide),h.empty .xa (by simp [boundaryFactorScratch])]; simp
  | pr => rw [hframe .pr (by decide),h.empty .pr (by simp [boundaryFactorScratch])]; simp
  | hc => rw [hframe .hc (by decide),h.empty .hc (by simp [boundaryFactorScratch])]; simp
  | ac => rw [hframe .ac (by decide),h.empty .ac (by simp [boundaryFactorScratch])]; simp
  | ac2 => rw [hframe .ac2 (by decide),h.empty .ac2 (by simp [boundaryFactorScratch])]; simp
  | nv => rw [hframe .nv (by decide),h.empty .nv (by simp [boundaryFactorScratch])]; simp
  | prm => rw [hframe .prm (by decide),hextra .prm (by simp)]; simp
  | dtab => rw [hframe .dtab (by decide),hextra .dtab (by simp)]; simp
  | padc => rw [hframe .padc (by decide),hextra .padc (by simp)]; simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
