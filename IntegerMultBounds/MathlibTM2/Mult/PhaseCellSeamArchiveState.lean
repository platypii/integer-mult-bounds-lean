module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamArchiveHandoff
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonPublicationReplicas
public import IntegerMultBounds.MathlibTM2.Host.RestoringSequence

/-! The remaining-archive invariant for structural seam publication. It carries
actual coefficient witnesses and byte layout while fixing the caller frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {T A s : ℕ} [NeZero s]

def SeamArchiveState (p width W : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (src dst : Fin T) (sourceTail outputTail : List (Fin (A+4))) (S : Stacks T A)
    (ks : List ℕ) (F : Stacks T A) : Prop :=
  ∃ banks : List (List (List GaussianInt)), ∃ ambient : List (List (Fin (A+4))),
    List.Forall₂ (SeamCropRows p width r J) ks banks ∧
    ambient.length = r.inputs.length ∧ (∀ line ∈ ambient, line.length = s*W) ∧
    F = {S with R := (Function.update (Function.update S.R src
      ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail))
      dst (ambient.flatten++outputTail))}

theorem SeamArchiveState.off (p width W : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (src dst : Fin T) (sourceTail outputTail : List (Fin (A+4))) (S F : Stacks T A)
    (ks : List ℕ) (h : SeamArchiveState p width W r J src dst sourceTail outputTail S ks F)
    (i : Fin T) (hs : i ≠ src) (hd : i ≠ dst) : F.R i = S.R i := by
  obtain ⟨banks,ambient,_,_,_,rfl⟩ := h
  simp only [Function.update_of_ne hd,Function.update_of_ne hs]

theorem SeamArchiveState.nil_source (p width W : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (src dst : Fin T) (hne : src ≠ dst) (sourceTail outputTail : List (Fin (A+4)))
    (S F : Stacks T A) (h : SeamArchiveState p width W r J src dst sourceTail outputTail S [] F) :
    F.R src = sourceTail := by
  obtain ⟨banks,ambient,hbanks,_,_,rfl⟩ := h
  have hnil : banks = [] := List.eq_nil_of_length_eq_zero (by simpa using hbanks.length_eq.symm)
  simp [hnil,Function.update_of_ne hne]

/-- A restoring singleton publication advances the archive invariant by one
bank; replica validity supplies the next ambient lengths. -/
theorem SeamArchiveState.step (p width W k : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (src dst : Fin T) (hne : src ≠ dst) (sourceTail outputTail : List (Fin (A+4)))
    (S : Stacks T A) (ks : List ℕ) (rows : List (List GaussianInt))
    (banks : List (List (List GaussianInt))) (hrows : SeamCropRows p width r J k rows)
    (hbanks : List.Forall₂ (SeamCropRows p width r J) ks banks)
    (windows : PublicationWindows s (coreLength s width k)) (hwindow : windows.origins.length = 1)
    (ambient : List (List (Fin (A+4)))) (hlen : ambient.length = r.inputs.length)
    (hambient : ∀ line ∈ ambient, line.length = s*W) :
    let replicas := singletonPublicationReplicas (rows.map (List.map (symZ (2*p+13)))) ambient
    let F : Stacks T A := {S with R := (Function.update (Function.update S.R src
      (((rows::banks).map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail))
      dst (ambient.flatten++outputTail))}
    SeamArchiveState p width W r J src dst sourceTail outputTail S ks
      {F with R := (Function.update (Function.update F.R src
        ((banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail))
        dst (replicas.flatMap (PublicationReplica.output windows W)++outputTail))} := by
  dsimp only
  let replicas := singletonPublicationReplicas (rows.map (List.map (symZ (2*p+13)))) ambient
  obtain ⟨hn,_,_,_,hvalid⟩ := seamPublicationReplicas_spec p width k W r J rows hrows
    windows hwindow ambient hlen hambient
  change replicas.length = r.inputs.length at hn
  refine ⟨banks,replicas.map (PublicationReplica.output windows W),hbanks,?_,?_,?_⟩
  · simpa only [List.length_map] using hn
  · intro line hline
    obtain ⟨replica,hr,rfl⟩ := List.mem_map.mp hline
    exact (hvalid replica hr).output_length
  · refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hd : i = dst
    · subst i; simp [List.flatMap_def,replicas]
    by_cases hs : i = src
    · subst i; simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hd,Function.update_of_ne hs]

/-- Consecutive stages retain one caller baseline even as source and ambient
bytes change. Only the inner stage's remaining certificates are needed. -/
theorem SeamArchiveState.rebase (p width W : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (src dst : Fin T) (sourceTail outputTail : List (Fin (A+4)))
    (S M F : Stacks T A) (previous remaining : List ℕ)
    (houter : SeamArchiveState p width W r J src dst sourceTail outputTail S previous M)
    (hinner : SeamArchiveState p width W r J src dst sourceTail outputTail M remaining F) :
    SeamArchiveState p width W r J src dst sourceTail outputTail S remaining F := by
  obtain ⟨oldBanks,oldAmbient,_,_,_,hM⟩ := houter
  obtain ⟨banks,ambient,hbanks,hlen,hambient,hF⟩ := hinner
  refine ⟨banks,ambient,hbanks,hlen,hambient,?_⟩
  rw [hF,hM]
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hd : i = dst
  · subst i; simp
  by_cases hs : i = src
  · subst i; simp [Function.update_of_ne hd]
  · simp [Function.update_of_ne hd,Function.update_of_ne hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
