module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPackedNormalizationLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPackedRecoveryNormalization

/-! The retained controls at the actual packed endpoint drive physical
normalization of either source. Both placements reuse the same workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open CyclicPackedNormalizationPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 907 Q A U}

def cyclicPackedPieceNormalization (right : Bool) : Pr P 907 Q A U :=
  PackedRecoveryNormalization.placedNormalizePiece (placement right)

def cyclicPackedNormalizationInput (S : Stacks 850 A) (wide : List (Fin (A+4))) : Stacks 907 A :=
  {extendStacks (by decide : 850 ≤ 907) S with R :=
    (Function.update (extendStacks (by decide : 850 ≤ 907) S).R 906 wide)}

theorem cyclicPackedPieceNormalization_exec (hA : 4 ≤ A) (right : Bool)
    {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (W : ℕ)
    (hpq : H.p ≤ H.precision)
    (hsize : H.precision-H.p+inverseNormalizationShift H.p+(2*H.p+13) ≤ 2*H.precision+8)
    (hW : 2*H.p+13 ≤ W)
    (active : Finset (ZMod s))
    (hactive : ∀ i ∈ active, H.origin ≤ i.val ∧ i.val < H.origin+H.span)
    (hcover : ∀ i : ZMod s, H.origin ≤ i.val → i.val < H.origin+H.span → i ∈ active)
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (e : ℝ) (he : e ≤ 1)
    (hx : ∀ x ∈ xs, ∀ i ∈ active, ‖x i‖ ≤ 4*(2 : ℝ)^(H.p+8))
    (hreal : ∀ D ∈ Ds, ∀ i, (D i).im = 0) (hfits : ∀ D ∈ Ds, ∀ i, Fits H.wordWidth (D i))
    (tail wide : List (Fin (A+4))) (hwide : wide.length = W)
    (hgood : List.Forall₂ (fun x D =>
      PhaseCellInterface.ErrorOn active (fun i => (value H.precision (D i)).re) x e) xs Ds)
    (v : HS 907 Q A U) (S : Stacks 850 A) (master : Fin 850)
    (controls : ReplicaAssemblyControls H (gather right) master S)
    (hsrc : S.R (source right) = (Ds.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++tail) :
    let E := cyclicPackedNormalizationInput S wide
    let Gs := Ds.map (fun D i => finalRoundWord H.wordWidth H.precision H.p (inverseNormalizationShift H.p) (D i))
    ∃ v' n, v'.user = v.user ∧
      n ≤ PackedRecoveryNormalization.normalizationCost H.p H.precision W H.origin H.span Ds.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v E)+0+
        PackedRecoveryNormalization.normalizationWorkspace H.p H.precision W H.origin H.span Ds.length) 0
        (cyclicPackedPieceNormalization right) (mk v E) n
        (mk v' {E with R := (Function.update E.R (extend (source right))
          ((Gs.map (fun D => cstream A W (packedInterval H.origin H.span D))).flatten++tail))}) ∧
      Exec body (cyclicPackedPieceNormalization right) (mk v E) n
        (mk v' {E with R := (Function.update E.R (extend (source right))
          ((Gs.map (fun D => cstream A W (packedInterval H.origin H.span D))).flatten++tail))}) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead H.p W H.origin (cstream A W (packedInterval H.origin H.span D)++tail))
        (fun i => ((2 : ℂ)^inverseNormalizationShift H.p)⁻¹*(x i : ℂ))
        (2/(2 : ℝ)^H.p+e/(2 : ℝ)^inverseNormalizationShift H.p)) xs Gs := by
  dsimp only
  let E := cyclicPackedNormalizationInput S wide
  have hread (i : Fin 850) : E.R (extend i) = S.R i := by
    have hne : extend i ≠ (906 : Fin 907) := by
      intro heq
      have hv := congrArg Fin.val heq
      change i.val = 906 at hv
      omega
    simp only [E,cyclicPackedNormalizationInput,Function.update_of_ne hne]
    exact congrArg (fun C : Stacks 850 A => C.R i) (embStk_extendStacks (by decide : 850 ≤ 907) S)
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := placement_old right
  have hwidth : H.wordWidth = 2*H.precision+8 := by
    simp only [ReplicaHaloProblem.wordWidth,ReplicaHaloProblem.precision,executionWidth,executionPrecision]
    omega
  obtain ⟨vf,n,hu,hn,hpieceWithin,hexec,haccuracy⟩ := PackedRecoveryNormalization.placedNormalizePiece_exec (body := body)
    (placement right) (placement_injective right) hA H.p H.precision W H.origin H.span hpq hsize hW
    H.span_fit active hactive hcover xs Ds e he hx hreal (by simpa only [hwidth] using hfits)
    tail hgood v E
    (by simpa only [h0,hread] using controls.kernel)
    (by simpa only [h1,hread] using controls.precision)
    (by simpa only [h2,hread] using controls.origin)
    (by simpa only [h3,hread] using controls.endpoint)
    (by simpa only [h4,hread,hwidth] using controls.volume)
    (by simpa only [h5,hread,hlen] using controls.replicas)
    (by simpa [h6,E,cyclicPackedNormalizationInput] using hwide)
    (by simpa only [h7,hread,hwidth] using hsrc)
    (by intro i hi
        have hf := placement_fresh right i hi
        have hne : placement right i ≠ 906 := by
          intro heq
          have hv := congrArg Fin.val heq
          omega
        simp only [E,cyclicPackedNormalizationInput,Function.update_of_ne hne]
        exact (extendStacks_fresh (by decide : 850 ≤ 907) S _ hf.1).2)
  exact ⟨vf,n,hu,hn,by simpa only [cyclicPackedPieceNormalization,E,h7,←hwidth] using hpieceWithin,by simpa only [cyclicPackedPieceNormalization,E,h7,←hwidth] using hexec,by simpa only [←hwidth] using haccuracy⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
