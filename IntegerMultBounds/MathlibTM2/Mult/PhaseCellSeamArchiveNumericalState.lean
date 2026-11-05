module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamArchiveState
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamPublicationPending

/-! One ambient-bank witness carries both byte framing and numerical progress. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement
variable {T A s : ℕ} [NeZero s]

def SeamArchiveNumericalState (p width W : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (classes : ℕ → CorePublicationClass s width)
    (src dst : Fin T) (sourceTail outputTail : List (Fin (A+4))) (S : Stacks T A)
    (ks : List ℕ) (F : Stacks T A) : Prop :=
  ∃ banks : List (List (List GaussianInt)), ∃ ambient : List (List (Fin (A+4))),
    List.Forall₂ (SeamCropRows p width r J) ks banks ∧
    PublicationBankPending (ks.map classes) p W (seamPublicationTargets p r J) (3/(2:ℝ)^p) ambient ∧
    F = {S with R := (Function.update (Function.update S.R src
      ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail))
      dst (ambient.flatten++outputTail))}

theorem SeamArchiveNumericalState.of_proper (p width W : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (classes : ℕ → CorePublicationClass s width) (proper : CorePublicationClass s width)
    (src dst : Fin T) (sourceTail outputTail : List (Fin (A+4))) (S : Stacks T A)
    (ks : List ℕ) (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p width r J) ks banks)
    (ambient : List (List (Fin (A+4))))
    (hcover : ∀ k ∈ coreIndices s width, ∃ c ∈ proper::ks.map classes, k ∈ c.indices)
    (hgood : List.Forall₂ (fun target line => line.length = s*W ∧
      ∀ k ∈ proper.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p W line) target (3/(2:ℝ)^p))
      (seamPublicationTargets p r J) ambient) :
    SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S ks
      {S with R := (Function.update (Function.update S.R src
        ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail))
        dst (ambient.flatten++outputTail))} :=
  ⟨banks,ambient,hbanks,PublicationBankPending.of_covered_class proper _ p W _ _ ambient hcover hgood,rfl⟩

theorem SeamArchiveNumericalState.forget (p width W : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (classes : ℕ → CorePublicationClass s width)
    (src dst : Fin T) (sourceTail outputTail : List (Fin (A+4))) (S F : Stacks T A)
    (ks : List ℕ)
    (h : SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S ks F) :
    SeamArchiveState p width W r J src dst sourceTail outputTail S ks F := by
  obtain ⟨banks,ambient,hbanks,hpending,hF⟩ := h
  refine ⟨banks,ambient,hbanks,?_,?_,hF⟩
  · simpa only [seamPublicationTargets,List.length_map,List.length_reverse] using hpending.length_eq.symm
  · have hflip := hpending.flip
    exact (List.forall₂_and_left _ _).mp hflip |>.1

theorem SeamArchiveNumericalState.finish (p width W : ℕ) (hw : 0 < width)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (classes : ℕ → CorePublicationClass s width)
    (src dst : Fin T) (hne : src ≠ dst) (sourceTail outputTail : List (Fin (A+4)))
    (S F : Stacks T A)
    (h : SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S [] F) :
    F.R src = sourceTail ∧
    ∃ ambient : List (List (Fin (A+4))), F.R dst = ambient.flatten++outputTail ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) ambient := by
  have hsource := SeamArchiveState.nil_source p width W r J src dst hne sourceTail outputTail S F
    (h.forget p width W r J classes src dst sourceTail outputTail S F [])
  obtain ⟨banks,ambient,hbanks,hpending,hF⟩ := h
  refine ⟨hsource,ambient,?_,?_⟩
  · rw [hF]
    simp
  · apply List.Forall₂.imp _ hpending
    intro target line hline
    refine ⟨hline.1,?_,?_⟩
    · have hb := CorePublicationPending.finish p W hw line (fun _ => 0) 1 hline.2.2
      simpa only [sub_zero] using hb
    · exact CorePublicationPending.finish p W hw line target (3/(2:ℝ)^p) hline.2.1

theorem SeamArchiveNumericalState.rebase (p width W : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (classes : ℕ → CorePublicationClass s width)
    (src dst : Fin T) (sourceTail outputTail : List (Fin (A+4)))
    (S M F : Stacks T A) (previous remaining : List ℕ)
    (houter : SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S previous M)
    (hinner : SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail M remaining F) :
    SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S remaining F := by
  obtain ⟨oldBanks,oldAmbient,_,_,hM⟩ := houter
  obtain ⟨banks,ambient,hbanks,hpending,hF⟩ := hinner
  refine ⟨banks,ambient,hbanks,hpending,?_⟩
  rw [hF,hM]
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hd : i = dst
  · subst i; simp
  by_cases hs : i = src
  · subst i; simp [Function.update_of_ne hd]
  · simp [Function.update_of_ne hd,Function.update_of_ne hs]

theorem SeamArchiveNumericalState.step (p width W k : ℕ) (hw : 0 < width)
    (hk : k ∈ coreIndices s width) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (classes : ℕ → CorePublicationClass s width)
    (hclass : classes k = singletonCorePublication s width k hk)
    (src dst : Fin T) (hne : src ≠ dst) (sourceTail outputTail : List (Fin (A+4)))
    (S : Stacks T A) (ks : List ℕ) (rows : List (List GaussianInt))
    (banks : List (List (List GaussianInt))) (hrows : SeamCropRows p width r J k rows)
    (hbanks : List.Forall₂ (SeamCropRows p width r J) ks banks)
    (ambient : List (List (Fin (A+4))))
    (hpending : PublicationBankPending ((k::ks).map classes) p W
      (seamPublicationTargets p r J) (3/(2:ℝ)^p) ambient) :
    let F : Stacks T A := {S with R := (Function.update (Function.update S.R src
      (((rows::banks).map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail))
      dst (ambient.flatten++outputTail))}
    let published := List.zipWith (fun row line =>
      (singletonCorePublication s width k hk).output W hw (fun _ => row) line)
      (rows.map (List.map (symZ (2*p+13)))) ambient
    SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S ks
      {F with R := (Function.update (Function.update F.R src
        ((banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail))
        dst (published.flatten++outputTail))} := by
  dsimp only
  simp only [List.map_cons,hclass] at hpending
  have hnext := seamPublication_bank_pending hw hk (ks.map classes) p W hA hW r J rows hrows ambient hpending
  refine ⟨banks,_,hbanks,hnext,?_⟩
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hd : i = dst
  · subst i; simp
  by_cases hs : i = src
  · subst i; simp [Function.update_of_ne hne]
  · simp [Function.update_of_ne hd,Function.update_of_ne hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
