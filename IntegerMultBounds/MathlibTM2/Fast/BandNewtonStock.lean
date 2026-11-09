module

public import IntegerMultBounds.MathlibTM2.Fast.BandFactor
public import IntegerMultBounds.MathlibTM2.Fast.CMulScalarBlockStock
public import IntegerMultBounds.MathlibTM2.Fast.ResampBScanStock
public import IntegerMultBounds.MathlibTM2.Fast.ResampBFrameStock
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock

/-! Newton reciprocal iterations replace one fixed-width word and restore their
scratch. All iterations therefore share one numerical step reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {Proc U : Type} {body : Proc → Pr Proc T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

@[irreducible] noncomputable def bandNewtonStepPush {P : Type} (rg : RsbR → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : ℕ :=
  mnProgPush (bandNewtonStepP (P := P) (Q := Q) (A := A) (U := U) rg hι hT hQ)

theorem bandNewtonStepP_native (rg : RsbR → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) :
    mnNativePushBound (bandNewtonStepPush (P := Proc) (A := A) (U := U) rg hι hT hQ)
      (bandNewtonStepP (P := Proc) (Q := Q) (A := A) (U := U) rg hι hT hQ) := by
  have hsub (a b o ctr tmp : Fin T) : WordCmd.NoCalls
      (rsbSubWord (P := Proc) (Q := Q) (A := A) (U := U) a b o ctr tmp) := by
    unfold rsbSubWord
    exact ⟨trivial,WordCmd.noCalls_of_native
      (autoWord_native _ _ _ _ _ _ _ (c := 2) (by decide) (by decide))⟩
  unfold bandNewtonStepPush
  apply WordCmd.native_of_noCalls _ (le_refl _)
  simp [bandNewtonStepP,cmulStream,cmulBlock_rmulOne_noCalls,rsbCopyTo,copyR,
    moveR,whileR,emptyR,hsub,WordCmd.NoCalls]

theorem band_newton_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P K : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (c : ℤ) (hfc : Fits w (⟨c, 0⟩ : GaussianInt))
    (hfit : ∀ n < K, Fits w (⟨Mult.BandFactor.newtonZ P c n, 0⟩ : GaussianInt) ∧
      Fits w (⟨(c*Mult.BandFactor.newtonZ P c n).tdiv (2^P), 0⟩ : GaussianInt))
    (hbx : σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P c 0, 0⟩)
    (hhv : σ .hv = csyms A w ⟨c, 0⟩) (hxa : σ .xa = [])
    (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = []) (hpr : σ .pr = []) (hac : σ .ac = [])
    (hac2 : σ .ac2 = []) (hnv : σ .nv = []) (hb1 : σ .b1 = []) (htC : σ .tC = [])
    (htA : σ .tA = []) (htK : σ .tK = []) (hkn : (σ .kn).length = K) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandNewtonP rg hι hT hQ) σ
      (Function.update σ .xa (csyms A w ⟨Mult.BandFactor.newtonZ P c K, 0⟩))
      (6 * w + 6 + (K * (bandNewtonStepCost w + 6) + 4))
      (2*(6*w+6)+bandNewtonStepPush (P := Proc) (A := A) (U := U) rg hι hT hQ*bandNewtonStepCost w) := by
  have hcsl : (csyms A w (⟨Mult.BandFactor.newtonZ P c 0, 0⟩ : GaussianInt)).length = w := by
    simp [csyms]
  have h₁ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .bx) (b := .xa)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ hb1 htC
  rw [hbx, hxa, List.append_nil, hcsl] at h₁
  have h₁w := h₁.within_native (rsbCopyTo_native (rg := rg) .bx .xa)
  set σ₁ := Function.update σ .xa (csyms A w ⟨Mult.BandFactor.newtonZ P c 0, 0⟩)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update σ .xa (csyms A w ⟨Mult.BandFactor.newtonZ P c j, 0⟩) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ₁ .kn).length, ∀ X Y, RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandNewtonStepP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .kn X .tK Y) (rsbUpd2 (Ψ (j + 1)) .kn X .tK Y) (bandNewtonStepCost w)
        (bandNewtonStepPush (P := Proc) (A := A) (U := U) rg hι hT hQ*bandNewtonStepCost w) := by
    intro j hj X Y
    have hj' : j < K := by simpa [σ₁, hkn] using hj
    have hready' : RsbReady (rsbUpd2 (Ψ j) .kn X .tK Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact ((hready.update .xa (fun c => by simp) _).update .kn (fun c => by simp) _).update .tK
        (fun c => by simp) _
    have hstep := band_newtonStep_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA
      (rsbUpd2 (Ψ j) .kn X .tK Y) hready' hw hp c (Mult.BandFactor.newtonZ P c j) hfc
      (hfit j hj').1 (hfit j hj').2 (by simp [rsbUpd2, hΨ, hhv]) (by simp [rsbUpd2, hΨ])
      (by simp [rsbUpd2, hΨ, hhc]) (by simp [rsbUpd2, hΨ, hya]) (by simp [rsbUpd2, hΨ, hxs])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hac]) (by simp [rsbUpd2, hΨ, hac2])
      (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, hb1]) (by simp [rsbUpd2, hΨ, htC])
      (by simp [rsbUpd2, hΨ, htA])
    refine (hstep.within_native (bandNewtonStepP_native rg hι hT hQ)).congr ?_
    funext r; cases r <;> simp [rsbUpd2, hΨ, newtonZ_succ]
  have hstock : ∀ j < (σ₁ .kn).length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) .kn X .tK Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) .kn X .tK Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S) := by
    intro j hj X Y v v' S F hS hF hf
    apply hS.size_le_of_lengths hF hf _ v v'
    intro r
    by_cases hk : r = .kn <;> by_cases ht : r = .tK <;> by_cases hx : r = .xa <;>
      simp [rsbUpd2,hΨ,Function.update_apply,hk,ht,hx]
  have h₂ := rsb_rep_runs_within hrg hdisj (ra := .kn) (rt := .tK) (by decide)
    (bandNewtonStepP rg hι hT hQ) (σ₁ .kn) Ψ _
    (bandNewtonStepPush (P := Proc) (A := A) (U := U) rg hι hT hQ*bandNewtonStepCost w) hbody hstock
  refine ((RsbRunsWithin.seq hdisj h₁w ((h₂.congr_pre ?_).congr ?_)).mono ?_ (le_refl _))
  · funext r; cases r <;> simp [rsbUpd2, hΨ, σ₁, htK]
  · funext r; cases r <;> simp [rsbUpd2, hΨ, σ₁, htK, hkn]
  · simp [σ₁, hkn]


end IntegerMultBounds.MathlibTM2.Fast
