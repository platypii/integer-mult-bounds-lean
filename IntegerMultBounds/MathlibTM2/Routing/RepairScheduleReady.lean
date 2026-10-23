module

public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigLoaderLayout
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedCallLoop
public import IntegerMultBounds.MathlibTM2.Host.ClassMove

/-! The concrete invariant between framed R2 calls. Arbitrary rank permutations
preserve its record shape and restore all reusable raw and scratch registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
variable {A M B : ℕ}

def repairStreamEffect (π : Equiv.Perm (Fin M)) (B : ℕ) (w : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  (List.range M).flatMap fun j => blk w B (permFun π.symm j)

structure RepairScheduleReady (M B : ℕ) (S : Stacks repairT A) : Prop where
  left : ∀ j, S.L j = []
  raw : ∀ key, S.R (repairSetupSource key) = []
  targets : ∀ key, S.R (repairSetupTarget key) = []
  blank : ∀ j, RepairBlank j → S.R j = []
  tmp : S.R repairConfigTmp = []
  stream : ∃ l : List (List (Fin (A + 4))), l.length = M ∧ (∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) ∧ S.R repairHost.src = l.flatten

theorem RepairScheduleReady.advance (S : Stacks repairT A) (ready : RepairScheduleReady M B S)
    (π : Equiv.Perm (Fin M)) (frame rest : List (Fin (A + 4))) :
    RepairScheduleReady M B { S with R := delimitedCallAdvanced S.R repairConfigInput repairConfigArchive repairHost.src frame rest (repairStreamEffect π B (S.R repairHost.src)) } := by
  have hkeep (j : Fin repairT) (hs : j ≠ repairConfigInput) (ha : j ≠ repairConfigArchive)
      (ht : j ≠ repairHost.src) :
      delimitedCallAdvanced S.R repairConfigInput repairConfigArchive repairHost.src frame rest
        (repairStreamEffect π B (S.R repairHost.src)) j = S.R j := by
    simp only [delimitedCallAdvanced, Function.update_of_ne hs, Function.update_of_ne ha, Function.update_of_ne ht]
  constructor <;> dsimp only
  · exact ready.left
  · intro key
    rw [hkeep _ (repairRawSource_setupSource 0 key).symm (repairRawSource_setupSource 2 key).symm
      (repairSetup_source_src key)]
    exact ready.raw key
  · intro key
    rw [hkeep _ (repairRawSource_setupTarget 0 key).symm (repairRawSource_setupTarget 2 key).symm
      (repairSetup_target_src key)]
    exact ready.targets key
  · intro j hj
    have hraw (f : Fin 6) : j ≠ repairRawSource f := by
      intro he
      subst j
      exact repairRawSource_not_blank f hj
    rw [hkeep j (hraw 0) (hraw 2) (repairBlank_src j hj)]
    exact ready.blank j hj
  · dsimp only [repairConfigTmp]
    rw [hkeep _ (repairRawSource_injective.ne (by decide : (1 : Fin 6) ≠ 0))
      (repairRawSource_injective.ne (by decide : (1 : Fin 6) ≠ 2)) (repairRawSource_src 1)]
    exact ready.tmp
  · obtain ⟨l, hl, hrecords, hstream⟩ := ready.stream
    refine ⟨moveRecs π l, length_moveRecs π l, ?_, ?_⟩
    · intro r hr
      exact hrecords r (mem_moveRecs π hl hr)
    · simp only [delimitedCallAdvanced, Function.update_self]
      rw [repairStreamEffect, hstream, ← flatten_moveRecs π l (fun r hr => (hrecords r hr).1)]

end IntegerMultBounds.MathlibTM2.Routing
