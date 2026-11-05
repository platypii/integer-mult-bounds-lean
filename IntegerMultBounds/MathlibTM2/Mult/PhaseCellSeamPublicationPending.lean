module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonPublicationClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationPending

/-! A certified seam overwrite advances both accuracy and unit-ball pending
invariants through the existing class proof, with no extra error term. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine ScalarPlacement PhaseCellInterface
variable {A s width k : ℕ} [NeZero s]

theorem singletonPublication_pending (hw : 0 < width) (hk : k ∈ coreIndices s width)
    (gs : List (CorePublicationClass s width)) (p W : ℕ)
    (row : List GaussianInt) (hrow : row.length = coreLength s width k)
    (ambient : List (Fin (A+4))) (hambient : ambient.length = s*W)
    (target : ZMod s → ℂ) (error : ℝ)
    (hgood : (∀ i ∈ ownedCore s width k,
      ‖packedIntervalRead p W (coreStart width k) (cstream A W row) i‖ ≤ 1) ∧
      ErrorOn (ownedCore s width k)
        (packedIntervalRead p W (coreStart width k) (cstream A W row)) target error)
    (hInv : CorePublicationPending (singletonCorePublication s width k hk::gs) p W ambient target error ∧
      CorePublicationPending (singletonCorePublication s width k hk::gs) p W ambient (fun _ => 0) 1) :
    let output := PublicationReplica.output (singletonCoreWindows hw hk) W
      (⟨[row],[row],ambient⟩ : PublicationReplica A)
    CorePublicationPending gs p W output target error ∧
      CorePublicationPending gs p W output (fun _ => 0) 1 := by
  dsimp only
  rw [singletonPublication_class_output]
  have hlength : ∀ j ∈ (singletonCorePublication s width k hk).indices,
      (row : List GaussianInt).length = (singletonCorePublication s width k hk).length := by
    intro j hj
    exact hrow
  constructor
  · apply CorePublicationPending.step _ gs p W hw (fun _ => row) hlength ambient hambient target error ?_ hInv.1
    intro j hj
    have hj' : j = k := by simpa [singletonCorePublication] using hj
    subst j
    exact hgood.2
  · apply CorePublicationPending.step _ gs p W hw (fun _ => row) hlength ambient hambient (fun _ => 0) 1 ?_ hInv.2
    intro j hj
    have hj' : j = k := by simpa [singletonCorePublication] using hj
    subst j
    intro i hi
    simpa only [sub_zero] using hgood.1 i hi

/-- Lift the singleton numerical step across aligned replica banks. -/
theorem singletonPublication_bank_pending (hw : 0 < width) (hk : k ∈ coreIndices s width)
    (gs : List (CorePublicationClass s width)) (p W : ℕ) (error : ℝ)
    (targets : List (ZMod s → ℂ)) (rows : List (List GaussianInt))
    (ambient : List (List (Fin (A+4))))
    (hrows : List.Forall₂ (fun target row =>
      row.length = coreLength s width k ∧
      (∀ i ∈ ownedCore s width k,
        ‖packedIntervalRead p W (coreStart width k) (cstream A W row) i‖ ≤ 1) ∧
      ErrorOn (ownedCore s width k)
        (packedIntervalRead p W (coreStart width k) (cstream A W row)) target error) targets rows)
    (hInv : List.Forall₂ (fun target line => line.length = s*W ∧
      CorePublicationPending (singletonCorePublication s width k hk::gs) p W line target error ∧
      CorePublicationPending (singletonCorePublication s width k hk::gs) p W line (fun _ => 0) 1)
      targets ambient) :
    List.Forall₂ (fun target line => line.length = s*W ∧
      CorePublicationPending gs p W line target error ∧
      CorePublicationPending gs p W line (fun _ => 0) 1) targets
      (List.zipWith (fun row line =>
        (singletonCorePublication s width k hk).output W hw (fun _ => row) line) rows ambient) := by
  induction hrows generalizing ambient with
  | nil => cases hInv; exact .nil
  | @cons target row targets rows hrow hrows ih =>
    cases hInv with
    | cons hline htail =>
      refine .cons ⟨?_,?_⟩ (ih _ htail)
      · exact (singletonCorePublication s width k hk).output_length W hw (fun _ => row)
          (by intro j hj; exact hrow.1) _ hline.1
      · have hnew := singletonPublication_pending hw hk gs p W row hrow.1 _ hline.1
          target error hrow.2 hline.2
        simpa only [singletonPublication_class_output] using hnew

def PublicationBankPending (gs : List (CorePublicationClass s width)) (p W : ℕ)
    (targets : List (ZMod s → ℂ)) (error : ℝ) (ambient : List (List (Fin (A+4)))) : Prop :=
  List.Forall₂ (fun target line => line.length = s*W ∧
    CorePublicationPending gs p W line target error ∧
    CorePublicationPending gs p W line (fun _ => 0) 1) targets ambient

theorem PublicationBankPending.of_covered_class (g : CorePublicationClass s width)
    (gs : List (CorePublicationClass s width)) (p W : ℕ)
    (targets : List (ZMod s → ℂ)) (error : ℝ) (ambient : List (List (Fin (A+4))))
    (hcover : ∀ k ∈ coreIndices s width, ∃ c ∈ g::gs, k ∈ c.indices)
    (hgood : List.Forall₂ (fun target line => line.length = s*W ∧
      ∀ k ∈ g.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        ErrorOn (ownedCore s width k) (pairedCellRead p W line) target error) targets ambient) :
    PublicationBankPending gs p W targets error ambient := by
  apply List.Forall₂.imp _ hgood
  intro target line hline
  refine ⟨hline.1,?_,?_⟩
  · exact CorePublicationPending.of_covered_class g gs p W line target error hcover
      (fun k hk => (hline.2 k hk).2)
  · apply CorePublicationPending.of_covered_class g gs p W line (fun _ => 0) 1 hcover
    intro k hk i hi
    simpa only [sub_zero] using (hline.2 k hk).1 i hi

noncomputable def seamPublicationTargets (p : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) :=
  r.inputs.reverse.map (fun input =>
    (((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r) ((1/2 : ℂ) • fun i => value p (input i)))

/-- Numerical preservation instantiated from the actual retained seam rows. -/
theorem seamPublication_bank_pending (hw : 0 < width) (hk : k ∈ coreIndices s width)
    (gs : List (CorePublicationClass s width)) (p W : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (hrows : SeamCropRows p width r J k rows)
    (ambient : List (List (Fin (A+4))))
    (hInv : List.Forall₂ (fun target line => line.length = s*W ∧
      CorePublicationPending (singletonCorePublication s width k hk::gs) p W line target (3/(2:ℝ)^p) ∧
      CorePublicationPending (singletonCorePublication s width k hk::gs) p W line (fun _ => 0) 1)
      (seamPublicationTargets p r J) ambient) :
    List.Forall₂ (fun target line => line.length = s*W ∧
      CorePublicationPending gs p W line target (3/(2:ℝ)^p) ∧
      CorePublicationPending gs p W line (fun _ => 0) 1)
      (seamPublicationTargets p r J)
      (List.zipWith (fun row line =>
        (singletonCorePublication s width k hk).output W hw (fun _ => row) line)
        (rows.map (List.map (symZ (2*p+13)))) ambient) := by
  obtain ⟨hlength,hgood⟩ := hrows.commonWidth p width W k hA hW r J rows
  apply singletonPublication_bank_pending hw hk gs p W _ _ _ ambient ?_ hInv
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_of_length_eq_of_get hgood.length_eq
  intro j hi hj
  exact ⟨hlength _ (List.getElem_mem hj),hgood.get hi hj⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
