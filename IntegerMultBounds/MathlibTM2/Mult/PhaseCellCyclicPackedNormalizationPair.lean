module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPackedNormalization

/-! Normalize both actual recovery archives using the same restored workspace.
Both packets retain the same ordered fields and the same normalization scale. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open CyclicPackedNormalizationPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 907 Q A U}

def cyclicPackedNormalization : Pr P 907 Q A U :=
  .seq (cyclicPackedPieceNormalization false) (cyclicPackedPieceNormalization true)

theorem cyclicPackedNormalization_exec (hA : 4 ≤ A)
    {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (hp : K.p = H.p) (hq : K.precision = H.precision) (W : ℕ)
    (hpq : H.p ≤ H.precision)
    (hsize : H.precision-H.p+inverseNormalizationShift H.p+(2*H.p+13) ≤ 2*H.precision+8)
    (hW : 2*H.p+13 ≤ W)
    (activeL activeR : Finset (ZMod s))
    (hactiveL : ∀ i ∈ activeL, H.origin ≤ i.val ∧ i.val < H.origin+H.span)
    (hcoverL : ∀ i : ZMod s, H.origin ≤ i.val → i.val < H.origin+H.span → i ∈ activeL)
    (hactiveR : ∀ i ∈ activeR, K.origin ≤ i.val ∧ i.val < K.origin+K.span)
    (hcoverR : ∀ i : ZMod s, K.origin ≤ i.val → i.val < K.origin+K.span → i ∈ activeR)
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt))
    (hlenL : Ds.length = H.Fs.length) (hlenR : Ds.length = K.Fs.length)
    (e : ℝ) (he : e ≤ 1)
    (hxL : ∀ x ∈ xs, ∀ i ∈ activeL, ‖x i‖ ≤ 4*(2 : ℝ)^(H.p+8))
    (hxR : ∀ x ∈ xs, ∀ i ∈ activeR, ‖x i‖ ≤ 4*(2 : ℝ)^(H.p+8))
    (hreal : ∀ D ∈ Ds, ∀ i, (D i).im = 0) (hfits : ∀ D ∈ Ds, ∀ i, Fits H.wordWidth (D i))
    (tailL tailR wide : List (Fin (A+4))) (hwide : wide.length = W)
    (hgoodL : List.Forall₂ (fun x D =>
      PhaseCellInterface.ErrorOn activeL (fun i => (value H.precision (D i)).re) x e) xs Ds)
    (hgoodR : List.Forall₂ (fun x D =>
      PhaseCellInterface.ErrorOn activeR (fun i => (value H.precision (D i)).re) x e) xs Ds)
    (v : HS 907 Q A U) (S : Stacks 850 A)
    (controlsL : ReplicaAssemblyControls H (gather false) 839 S)
    (controlsR : ReplicaAssemblyControls K (gather true) 838 S)
    (hsrcL : S.R 848 = (Ds.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++tailL)
    (hsrcR : S.R 849 = (Ds.map (fun D => cstream A K.wordWidth (packedInterval K.origin K.span D))).flatten++tailR) :
    let E := cyclicPackedNormalizationInput S wide
    let Gs := Ds.map (fun D i => finalRoundWord H.wordWidth H.precision H.p (inverseNormalizationShift H.p) (D i))
    ∃ v' n, v'.user = v.user ∧
      n ≤ PackedRecoveryNormalization.normalizationCost H.p H.precision W H.origin H.span Ds.length+
        PackedRecoveryNormalization.normalizationCost K.p K.precision W K.origin K.span Ds.length ∧
      Exec body cyclicPackedNormalization (mk v E) n
        (mk v' {E with R := (Function.update (Function.update E.R 848
          ((Gs.map (fun D => cstream A W (packedInterval H.origin H.span D))).flatten++tailL)) 849
          ((Gs.map (fun D => cstream A W (packedInterval K.origin K.span D))).flatten++tailR))}) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn activeL
        (packedIntervalRead H.p W H.origin (cstream A W (packedInterval H.origin H.span D)++tailL))
        (fun i => ((2 : ℂ)^inverseNormalizationShift H.p)⁻¹*(x i : ℂ))
        (2/(2 : ℝ)^H.p+e/(2 : ℝ)^inverseNormalizationShift H.p)) xs Gs ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn activeR
        (packedIntervalRead H.p W K.origin (cstream A W (packedInterval K.origin K.span D)++tailR))
        (fun i => ((2 : ℂ)^inverseNormalizationShift H.p)⁻¹*(x i : ℂ))
        (2/(2 : ℝ)^H.p+e/(2 : ℝ)^inverseNormalizationShift H.p)) xs Gs := by
  dsimp only
  let E := cyclicPackedNormalizationInput S wide
  let Gs := Ds.map (fun D i => finalRoundWord H.wordWidth H.precision H.p (inverseNormalizationShift H.p) (D i))
  let wordsL := (Gs.map (fun D => cstream A W (packedInterval H.origin H.span D))).flatten++tailL
  let S' : Stacks 850 A := {S with R := Function.update S.R 848 wordsL}
  have hw : K.wordWidth = H.wordWidth := by
    have hword (J : ReplicaHaloProblem s) : J.wordWidth = 2*J.precision+8 := by
      simp only [ReplicaHaloProblem.wordWidth,ReplicaHaloProblem.precision,executionWidth,executionPrecision]
      omega
    rw [hword K,hword H,hq]
  obtain ⟨vi,m,huL,hmL,heL,haccuracyL⟩ := cyclicPackedPieceNormalization_exec (body := body)
    hA false H W hpq hsize hW activeL hactiveL hcoverL xs Ds hlenL e he hxL hreal hfits
    tailL wide hwide hgoodL v S 839 controlsL hsrcL
  have controlsR' : ReplicaAssemblyControls K (gather true) 838 S' := by
    apply controlsR.transport (F := S') (gather' := gather true)
    · rfl
    · intro i hi
      have hne : gather true i ≠ (848 : Fin 850) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
      exact Function.update_of_ne hne _ _
  have hinput : cyclicPackedNormalizationInput S' wide =
      {E with R := Function.update E.R 848 wordsL} := by
    dsimp only [cyclicPackedNormalizationInput,S']
    rw [extendStacks_updateR]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h906 : i = 906 <;> by_cases h848 : i = 848 <;>
      simp [E,cyclicPackedNormalizationInput,h906,h848]
  obtain ⟨vf,n,huR,hmR,heR,haccuracyR⟩ := cyclicPackedPieceNormalization_exec (body := body)
    hA true K W (by simpa only [hp,hq] using hpq) (by simpa only [hp,hq] using hsize)
    (by simpa only [hp] using hW) activeR hactiveR hcoverR xs Ds hlenR e he
    (by simpa only [hp] using hxR) hreal (by simpa only [hw] using hfits)
    tailR wide hwide (by simpa only [hq] using hgoodR) vi S' 838 controlsR'
    (by simpa [S',source] using hsrcR)
  rw [hinput] at heR
  have h849 : extend (849 : Fin 850) = (849 : Fin 907) := by decide +kernel
  refine ⟨vf,m+n,huR.trans huL,Nat.add_le_add hmL hmR,?_,haccuracyL,?_⟩
  · simpa only [cyclicPackedNormalization,source,Bool.false_eq_true,ite_false,ite_true,
      hp,hq,hw,E,Gs,wordsL,h849] using Exec.seq heL heR
  · simpa only [hp,hq,hw] using haccuracyR

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
