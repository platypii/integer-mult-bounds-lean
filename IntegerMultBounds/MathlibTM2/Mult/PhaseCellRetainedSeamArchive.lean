module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreArchiveRows
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Reuse one full-line solve for seam crops. A full-period certificate restricts
to every core; each actual crop restores the owned full-line output and replica
clock. Extra copies are charged as stream movement, never as numerical setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Fast.Main ScalarPlacement PhaseCellInterface
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem ownedCore_entire : ownedCore s s 0 = Finset.univ := by
  ext i
  simp only [ownedCore,coreStart,coreLength,Nat.zero_mul,Nat.sub_zero,Nat.min_self,Nat.zero_add,mem_haloVertices,Finset.mem_univ,iff_true]
  exact ⟨Nat.zero_le _,i.val_lt⟩

/-- A full-period core forces its generated halo to be the whole system,
independently of the selected locality depth and band. -/
theorem generatedWindow_entire (p u target : ℕ) :
    (generatedWindow s s p u target 0).halo = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  apply (generatedWindow s s p u target 0).core_subset_halo
  change i ∈ ownedCore s s 0
  rw [ownedCore_entire]
  exact Finset.mem_univ i

/-- The ordinary full-line descriptor supplies the generated-window ABI.
No seam-specific local solution or locality hypothesis is needed. -/
theorem fullLine_generated_halo (p u target : ℕ) :
    haloVertices s 0 s = (generatedWindow s s p u target 0).halo := by
  rw [generatedWindow_entire]
  ext i
  simp only [mem_haloVertices,Finset.mem_univ,iff_true]
  exact ⟨Nat.zero_le _,i.val_lt⟩

theorem ExactCoreProduced.restrict_full {p : ℕ} {r : FamilyDispatchInput s A}
    {J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} {output : List (Fin (A+4))}
    (h : ExactCoreProduced p s (fun _ => 0) J r output) (coreWidth k : ℕ) :
    ExactCoreProduced p coreWidth (fun _ => k) J r output := by
  obtain ⟨Ds,houtput,hgood⟩ := h
  refine ⟨Ds,houtput,hgood.imp ?_⟩
  intro input D hD
  constructor
  · intro i _; exact hD.1 i (by rw [ownedCore_entire]; exact Finset.mem_univ _)
  · intro i _; exact hD.2 i (by rw [ownedCore_entire]; exact Finset.mem_univ _)

def retainedSeamArchive
    (clock clockSave sourceSave skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T) : Pr P T Q A U :=
  .seq (copyR src sourceSave tmp id) (.seq (copyR clock clockSave tmp id)
    (.seq (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
      (.seq (moveR sourceSave src id) (moveR clockSave clock id))))

theorem retainedSeamArchive_exec
    (clock clockSave sourceSave skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [clock,clockSave,sourceSave,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (p coreWidth k : ℕ)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (output : List (Fin (A+4)))
    (hproduced : ExactCoreProduced p s (fun _ => 0) J r output)
    (hstart : coreStart coreWidth k ≤ s)
    (hsrc : S.R src = output) (hclock : (S.R clock).length = r.inputs.length)
    (hskip : (S.R skip).length = coreStart coreWidth k*(2*p+13))
    (hcount : (S.R count).length = coreLength s coreWidth k*(2*p+13))
    (hrows : (S.R rows).length = s) (hwidth : (S.R width).length = 2*p+13)
    (hclean : ∀ i ∈ [clockSave,sourceSave,savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ coreRows : List (List GaussianInt), ∃ v' F n, v'.user = v.user ∧
      n ≤ r.inputs.length*(packedCoreArchiveStepCost (coreStart coreWidth k) (coreLength s coreWidth k) s (2*p+13)+3)+2+
        6*output.length+6*r.inputs.length+12 ∧
      Exec body (retainedSeamArchive clock clockSave sourceSave skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R dst = cstream A (2*p+13) coreRows.flatten++S.R dst ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧ (∀ i, i ≠ dst → F.R i = S.R i) ∧
      (∀ row ∈ coreRows, row.length = coreLength s coreWidth k) ∧
      List.Forall₂ (fun input row =>
        let out := packedIntervalRead p (2*p+13) (coreStart coreWidth k) (cstream A (2*p+13) row)
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r) ((1/2 : ℂ) • fun i => value p (input i)))
          (3/(2 : ℝ)^p)) r.inputs.reverse coreRows := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) src sourceSave tmp ‹sourceSave ≠ src›.symm ‹src ≠ tmp› ‹sourceSave ≠ tmp› id v S
    (hclean _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R sourceSave output.reverse}
  have he₁' : Exec body (copyR src sourceSave tmp id) (mk v S) (4*output.length+4) (mk v₁ M) := by
    simpa only [hsrc,List.map_id,hclean sourceSave (by simp),List.append_nil] using he₁
  have hM (i : Fin T) (hi : i ≠ sourceSave) : M.R i = S.R i := by simp [M,hi]
  obtain ⟨v₂,hu₂,he₂⟩ := copyR_exec (body := body) clock clockSave tmp ‹clock ≠ clockSave› ‹clock ≠ tmp› ‹clockSave ≠ tmp› id v₁ M
    (by rw [hM _ ‹sourceSave ≠ tmp›.symm]; exact hclean _ (by simp))
  let N : Stacks T A := {M with R := Function.update M.R clockSave (S.R clock).reverse}
  have he₂' : Exec body (copyR clock clockSave tmp id) (mk v₁ M) (4*r.inputs.length+4) (mk v₂ N) := by
    simpa only [hM _ ‹clock ≠ sourceSave›,hM _ ‹clockSave ≠ sourceSave›,hclean clockSave (by simp),List.map_id,List.append_nil,hclock] using he₂
  have hN (i : Fin T) (hi : i ≠ sourceSave) (hc : i ≠ clockSave) : N.R i = S.R i := by simp [N,M,hi,hc]
  obtain ⟨coreRows,v₃,F,n₃,hu₃,hn₃,he₃,hs,hd,hc,hi,ho,hl,hframe,hlen,hgood⟩ := exactCoreArchive_rows_exec (body := body)
    clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp (by regs_nodup) v₂ N p coreWidth k r J output
    (ExactCoreProduced.restrict_full hproduced coreWidth k) hstart []
    (by rw [hN _ ‹sourceSave ≠ src›.symm ‹clockSave ≠ src›.symm]; simpa using hsrc)
    (by rw [hN _ ‹clock ≠ sourceSave› ‹clock ≠ clockSave›]; exact hclock)
    (by rw [hN _ ‹sourceSave ≠ skip›.symm ‹clockSave ≠ skip›.symm]; exact hskip)
    (by rw [hN _ ‹sourceSave ≠ count›.symm ‹clockSave ≠ count›.symm]; exact hcount)
    (by rw [hN _ ‹sourceSave ≠ rows›.symm ‹clockSave ≠ rows›.symm]; exact hrows)
    (by rw [hN _ ‹sourceSave ≠ width›.symm ‹clockSave ≠ width›.symm]; exact hwidth)
    (by
      intro i hi
      have hoff : i ≠ sourceSave ∧ i ≠ clockSave := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals constructor <;> first | assumption | (apply Ne.symm; assumption)
      rw [hN i hoff.1 hoff.2]
      apply hclean i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      exact Or.inr (Or.inr hi))
  have hss : F.R sourceSave = output.reverse := by
    rw [hframe _ ‹sourceSave ≠ src› ‹sourceSave ≠ dst› ‹clock ≠ sourceSave›.symm]
    simp [N,M,‹clockSave ≠ sourceSave›.symm]
  have hcs : F.R clockSave = (S.R clock).reverse := by
    rw [hframe _ ‹clockSave ≠ src› ‹clockSave ≠ dst› ‹clock ≠ clockSave›.symm]
    simp [N]
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body sourceSave src ‹sourceSave ≠ src› id v₃ F
  let G : Stacks T A := {F with R := movedR F.R sourceSave src id (F.R sourceSave)}
  have he₄' : Exec body (moveR sourceSave src id) (mk v₃ F) (2*output.length+2) (mk v₄ G) := by
    simpa only [G,hss,List.length_reverse] using he₄
  have hgc : G.R clockSave = (S.R clock).reverse := by simp [G,movedR,‹clockSave ≠ sourceSave›,‹clockSave ≠ src›,hcs]
  have hGclock : G.R clock = [] := by simp [G,movedR,‹clock ≠ sourceSave›,‹clock ≠ src›,hc]
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body clockSave clock ‹clock ≠ clockSave›.symm id v₄ G
  let H : Stacks T A := {G with R := movedR G.R clockSave clock id (G.R clockSave)}
  have he₅' : Exec body (moveR clockSave clock id) (mk v₄ G) (2*r.inputs.length+2) (mk v₅ H) := by
    simpa only [H,hgc,List.length_reverse,hclock] using he₅
  refine ⟨coreRows,v₅,H,(4*output.length+4)+((4*r.inputs.length+4)+(n₃+((2*output.length+2)+(2*r.inputs.length+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),by omega,
    Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' he₅'))),?_,hi,ho,hl,?_,hlen,hgood⟩
  · simpa [H,G,movedR,‹clockSave ≠ dst›.symm,‹clock ≠ dst›.symm,‹sourceSave ≠ dst›.symm,‹src ≠ dst›.symm,hN dst ‹sourceSave ≠ dst›.symm ‹clockSave ≠ dst›.symm] using hd
  · intro i hid
    by_cases his : i = src
    · subst i; simp [H,G,movedR,hss,hs,hsrc,‹clockSave ≠ src›.symm,‹clock ≠ src›.symm]
    · by_cases hic : i = clock
      · subst i; simp [H,movedR,hgc,hGclock]
      · by_cases hiz : i = sourceSave
        · subst i; simp [H,G,movedR,‹clockSave ≠ sourceSave›.symm,‹clock ≠ sourceSave›.symm,‹sourceSave ≠ src›,hclean sourceSave (by simp)]
        · by_cases hiq : i = clockSave
          · subst i; simp [H,movedR,‹clock ≠ clockSave›.symm,hclean clockSave (by simp)]
          · simp only [H,G,movedR,Function.update_of_ne hic,Function.update_of_ne hiq,Function.update_of_ne his,Function.update_of_ne hiz]
            rw [hframe i his hid hic,hN i hiz hiq]

theorem ExactCoreProduced.full_output_length {p : ℕ} {r : FamilyDispatchInput s A}
    {J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} {output : List (Fin (A+4))}
    (h : ExactCoreProduced p s (fun _ => 0) J r output) : output.length = r.inputs.length*s*(2*p+13) := by
  obtain ⟨Ds,houtput,hgood⟩ := h
  have hl : ∀ row ∈ Ds.map (chirpLine s), row.length = s := by
    intro row hr
    obtain ⟨D,_,rfl⟩ := List.mem_map.mp hr
    exact length_chirpLine _ _
  rw [houtput,FamilyDispatchInput.normalizedOutput,length_cstream,length_flatten_const _ hl,List.length_map,←hgood.length_eq]

theorem retainedSeamArchive_native
    (clock clockSave sourceSave skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T) :
    mnNativePushBound 2 (retainedSeamArchive (P := P) (Q := Q) (A := A) (U := U)
      clock clockSave sourceSave skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp) := by
  simp [retainedSeamArchive,packedCoreArchiveLoop,packedCoreArchiveStep,copySlice,copyPrefix,copyR,copyStep,
    countedLoop,countedLoopBody,retireCountedLine,discardPrefix,unaryProduct,scanP,ucopy,umulSym,transfer,moveR,uclear,keepIn,
    scanR,transferAct,drainR,popDo,whileR,moveStep,peekR,pushN,popPush,mnNativePushBound,mnActPush]

theorem retainedSeamArchive_within
    {clock clockSave sourceSave skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T}
    {v v' : HS T Q A U} {S F : Stacks T A} {n bound : ℕ}
    (he : Exec body (retainedSeamArchive clock clockSave sourceSave skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
      (mk v S) n (mk v' F)) (hn : n ≤ bound) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*bound) depth
      (retainedSeamArchive clock clockSave sourceSave skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
      (mk v S) n (mk v' F) := by
  exact mn_native_exec_within he 2 (retainedSeamArchive_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega)

/-- Reusing a full-line result for one seam crop has linear movement cost.
The endpoint scans, full-result backup, and clock restoration are all included. -/
theorem retainedSeamArchiveCost_linear (B s a c w : ℕ) (hs : 1 ≤ s) (hw : 1 ≤ w)
    (ha : a ≤ s) (hc : c ≤ s) :
    B*(packedCoreArchiveStepCost a c s w+3)+2+6*(B*s*w)+6*B+12 ≤ 80*(B*s*w)+14 := by
  have haw := Nat.mul_le_mul_right w ha
  have hcw := Nat.mul_le_mul_right w hc
  have hsw : 1 ≤ s*w := Nat.mul_pos hs hw
  have hs' : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw
  have hstep : packedCoreArchiveStepCost a c s w+3+6*(s*w)+6 ≤ 80*(s*w) := by
    dsimp only [packedCoreArchiveStepCost,retireCountedLineCost]
    nlinarith only [haw,hcw,hsw,hs']
  have hb := Nat.mul_le_mul_left B hstep
  nlinarith only [hb]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
