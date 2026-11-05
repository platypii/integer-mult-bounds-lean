module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationGroups

/-! The actual class publication endpoint supplies the bank contract consumed
by boundary completion. This is structural in the replica list and class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {A s width : ℕ} [NeZero s]

theorem CorePublicationClass.output_norm_le (g : CorePublicationClass s width) (p W : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt) (hrows : ∀ k ∈ g.indices, (rows k).length = g.length)
    (ambient : List (Fin (A+4))) (hlen : ambient.length = s*W)
    (hgood : ∀ k ∈ g.indices, ∀ i ∈ ownedCore s width k,
      ‖packedIntervalRead p W (coreStart width k) (cstream A W (rows k)) i‖ ≤ 1)
    (k : ℕ) (hk : k ∈ g.indices) :
    ∀ i ∈ ownedCore s width k, ‖pairedCellRead p W (g.output W hw rows ambient) i‖ ≤ 1 := by
  have hzero : ∀ k ∈ g.indices, PhaseCellInterface.ErrorOn (ownedCore s width k)
      (packedIntervalRead p W (coreStart width k) (cstream A W (rows k))) (fun _ => 0) 1 := by
    intro k hk i hi
    simpa only [sub_zero] using hgood k hk i hi
  have hout := g.output_errorOn p W hw rows hrows ambient hlen (fun _ => 0) 1 hzero k hk
  intro i hi
  simpa only [sub_zero] using hout i hi

theorem CorePublicationClass.output_bank_good (g : CorePublicationClass s width) (p W : ℕ) (hw : 0 < width)
    {N : ℕ} (targets : Fin N → ZMod s → ℂ) (error : ℝ)
    (rows : Fin N → ℕ → List GaussianInt)
    (ambient : Fin N → List (Fin (A+4)))
    (hrows : ∀ j k, k ∈ g.indices → (rows j k).length = g.length)
    (hlen : ∀ j, (ambient j).length = s*W)
    (hgood : ∀ j k, k ∈ g.indices →
      (∀ i ∈ ownedCore s width k,
        ‖packedIntervalRead p W (coreStart width k) (cstream A W (rows j k)) i‖ ≤ 1) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead p W (coreStart width k) (cstream A W (rows j k))) (targets j) error) :
    List.Forall₂ (fun target line => line.length = s*W ∧
      ∀ k ∈ g.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p W line) target error)
      (List.ofFn targets) (List.ofFn (fun j => g.output W hw (rows j) (ambient j))) := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro j hj houtput
  simp only [List.length_ofFn] at hj houtput
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  refine ⟨g.output_length W hw _ (hrows ⟨j,hj⟩) _ (hlen ⟨j,hj⟩),?_⟩
  intro k hk
  exact ⟨g.output_norm_le p W hw _ (hrows ⟨j,hj⟩) _ (hlen ⟨j,hj⟩)
      (fun k hk => (hgood ⟨j,hj⟩ k hk).1) k hk,
    g.output_errorOn p W hw _ (hrows ⟨j,hj⟩) _ (hlen ⟨j,hj⟩) _ error
      (fun k hk => (hgood ⟨j,hj⟩ k hk).2) k hk⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
