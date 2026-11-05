module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedSeamPublicationPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders

/-! Copy retained caller headers into the private seam bank. The eleven words
are replica/line/word rulers, binary dimensions, arithmetic width and crop counts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def boundarySeamMasterRole : Fin 11 → Fin 117 := ![15,16,17,18,55,56,57,58,60,61,62]

theorem boundarySeamMasterRole_injective : Function.Injective boundarySeamMasterRole := by
  decide +kernel

theorem boundarySeamMasterRole_off :
    ∀ i, boundarySeamMasterRole i ∉ [(95:Fin 117),96,27,28] := by decide +kernel

namespace PackedTranspose
noncomputable section

theorem seamRegister_prefix_ne_private (source destination j : Fin T) (i : Fin 117)
    (hs : i ≠ 95) (hd : i ≠ 96) :
    Fin.castAdd tapeCount j ≠ seamRegister source destination i := by
  rw [seamRegister_private source destination i hs hd]
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have := j.isLt
  omega

end
end PackedTranspose

noncomputable section
open PackedTranspose

def boundarySeamMasterCopies (source destination : Fin T) (masters : Fin 11 → Fin T) :=
  List.ofFn (fun i => (Fin.castAdd tapeCount (masters i),
    seamRegister source destination (boundarySeamMasterRole i)))

def boundarySeamMasterLoad (source destination : Fin T) (masters : Fin 11 → Fin T) :
    Pr P (T+tapeCount) Q A U :=
  copyWordHeaders (seamRegister source destination 27) (seamRegister source destination 28)
    (boundarySeamMasterCopies source destination masters)

theorem boundarySeamMasterLoad_native (source destination : Fin T) (masters : Fin 11 → Fin T) :
    mnNativePushBound 2
      (boundarySeamMasterLoad (P := P) (Q := Q) (A := A) (U := U) source destination masters) :=
  copyWordHeaders_native _ _ _

theorem boundarySeamMasterLoad_exec (body : P → Pr P (T+tapeCount) Q A U)
    (source destination : Fin T) (hne : source ≠ destination) (masters : Fin 11 → Fin T)
    (v : HS (T+tapeCount) Q A U) (S : Stacks (T+tapeCount) A)
    (htmp : S.R (seamRegister source destination 27) = [])
    (hsaved : S.R (seamRegister source destination 28) = [])
    (hblank : ∀ i, S.R (seamRegister source destination (boundarySeamMasterRole i)) = []) :
    let pairs := boundarySeamMasterCopies source destination masters
    let F : Stacks (T+tapeCount) A := {S with R := copyWordHeadersR S.R pairs S.R}
    ∃ v', v'.user = v.user ∧
      (∀ i, F.R (seamRegister source destination (boundarySeamMasterRole i)) =
        S.R (Fin.castAdd tapeCount (masters i))) ∧
      (∀ i, (∀ j, seamRegister source destination (boundarySeamMasterRole j) ≠ i) → F.R i = S.R i) ∧
      Exec body (boundarySeamMasterLoad source destination masters) (mk v S)
        ((pairs.map (fun r => 6*(S.R r.1).length+6)).sum+1) (mk v' F) := by
  dsimp only
  let e := seamRegister source destination
  have hinj := seamRegister_injective source destination hne
  have hrole (i : Fin 11) : boundarySeamMasterRole i ≠ 27 ∧ boundarySeamMasterRole i ≠ 28 := by
    have h := boundarySeamMasterRole_off i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact h.2.2
  have hprefix (j : Fin T) (i : Fin 11) : Fin.castAdd tapeCount j ≠ e (boundarySeamMasterRole i) := by
    apply seamRegister_prefix_ne_private source destination j
    · have h := boundarySeamMasterRole_off i
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      exact h.1
    · have h := boundarySeamMasterRole_off i
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      exact h.2.1
  obtain ⟨v',hu,he⟩ := copyWordHeaders_exec (body := body) (e 27) (e 28)
    (boundarySeamMasterCopies source destination masters)
    (by
      intro r hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,not_false_eq_true,and_true]
      exact ⟨⟨hprefix _ i,seamRegister_prefix_ne_private source destination _ 27 (by decide) (by decide),
        seamRegister_prefix_ne_private source destination _ 28 (by decide) (by decide)⟩,
        ⟨hinj.ne (hrole i).1,hinj.ne (hrole i).2⟩,hinj.ne (by decide)⟩)
    (by
      intro r hr p hp
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
      exact (hprefix _ i).symm)
    S.R v S (by intro r hr; rfl) htmp hsaved
  refine ⟨v',hu,?_,?_,he⟩
  · intro i
    have hnd : ((boundarySeamMasterCopies source destination masters).map Prod.snd).Nodup := by
      rw [boundarySeamMasterCopies,List.map_ofFn]
      exact List.nodup_ofFn.mpr (hinj.comp boundarySeamMasterRole_injective)
    have hget := copyWordHeadersR_get S.R (boundarySeamMasterCopies source destination masters)
      hnd S.R _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa only [hblank i,List.append_nil] using hget
  · intro i hi
    apply copyWordHeadersR_off
    intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact hi j

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
