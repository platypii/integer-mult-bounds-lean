module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationGroups
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowScatter
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Actual ordered class publication from prepared control tapes. Each scatter
restores all controls and scratch, deriving the next class's readiness directly
from its exact source/destination frame. Control preparation is charged separately. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A s width : ℕ} {P U : Type}

def corePublicationGroupsProgram
    (control window : CorePublicationClass s width → Fin T)
    (savedControl gap src dst acc trash tmp : Fin T) : List (CorePublicationClass s width) → Pr P T Q A U
  | [] => .act .done
  | g::gs => .seq (scatterBatch (control g) savedControl gap (window g) src dst acc trash tmp)
      (corePublicationGroupsProgram control window savedControl gap src dst acc trash tmp gs)

theorem corePublicationGroups_exec (body : P → Pr P T Q A U)
    (control window : CorePublicationClass s width → Fin T)
    (savedControl gap src dst acc trash tmp : Fin T)
    (gs : List (CorePublicationClass s width))
    (hreg : ∀ g ∈ gs, [control g,savedControl,gap,window g,src,dst,acc,trash,tmp].Nodup)
    (w : ℕ) (hw : 0 < width)
    (rows : CorePublicationClass s width → ℕ → List GaussianInt)
    (hrows : ∀ g ∈ gs, ∀ k ∈ g.indices, (rows g k).length = g.length)
    (E sourceTail outputTail : List (Fin (A+4))) (hE : E.length = s*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : ∀ g ∈ gs, S.R (control g) = gatherControls A ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps w))
    (hwindows : ∀ g ∈ gs, (S.R (window g)).length = g.length*w)
    (hsrc : S.R src = gs.flatMap (fun g => cstream A w (g.indices.map (rows g)).flatten)++sourceTail)
    (hdst : S.R dst = E++outputTail)
    (hclean : ∀ i ∈ [savedControl,gap,acc,trash,tmp], S.R i = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (corePublicationGroupsProgram control window savedControl gap src dst acc trash tmp gs)
        (mk v S) (corePublicationGroupsCost w hw gs+1)
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail)
          dst (corePublicationGroupsOutput w hw rows gs E++outputTail))}) := by
  induction gs generalizing v S E with
  | nil =>
    have hs : S.R src = sourceTail := by simpa using hsrc
    have hd : S.R dst = E++outputTail := hdst
    refine ⟨v,rfl,?_⟩
    simpa only [corePublicationGroupsProgram,corePublicationGroupsCost,List.map_nil,List.sum_nil,
      corePublicationGroupsOutput,Action.run,Nat.zero_add,←hs,Function.update_eq_self,←hd] using
      Exec.act (body := body) (.done : Act T Q A U) (mk v S)
  | cons g gs ih =>
    have hr := hreg g (by simp)
    regs_ne hr
    let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
    let tail := gs.flatMap (fun g => cstream A w (g.indices.map (rows g)).flatten)++sourceTail
    obtain ⟨v₁,hu₁,he₁⟩ := windowScatter_exec (body := body) (hreg g (by simp)) windows w E
      (cstream A w (g.indices.map (rows g)).flatten) tail outputTail hE
      (by simpa only [windows,coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map] using
        g.source_length (A := A) w (rows g) (hrows g (by simp))) v S
      (hc g (by simp)) hdst (by simpa only [List.flatMap_cons,List.append_assoc,tail] using hsrc)
      (hwindows g (by simp)) hclean
    let E₁ := g.output w hw (rows g) E
    let M : Stacks T A := {S with R := Function.update (Function.update S.R src tail) dst (E₁++outputTail)}
    have hstable (i : Fin T) (his : i ≠ src) (hid : i ≠ dst) : M.R i = S.R i := by simp [M,his,hid]
    have hoff (g' : CorePublicationClass s width) (hg' : g' ∈ gs) :
        control g' ≠ src ∧ control g' ≠ dst ∧ window g' ≠ src ∧ window g' ≠ dst := by
      have hr' := hreg g' (by simp [hg'])
      regs_ne hr'
      exact ⟨by assumption,by assumption,by assumption,by assumption⟩
    obtain ⟨v₂,hu₂,he₂⟩ := ih (fun g hg => hreg g (by simp [hg]))
      (fun g hg => hrows g (by simp [hg])) E₁ (g.output_length w hw (rows g) (hrows g (by simp)) E hE) v₁ M
      (by intro g' hg'; rw [hstable _ (hoff g' hg').1 (hoff g' hg').2.1]; exact hc g' (by simp [hg']))
      (by intro g' hg'; rw [hstable _ (hoff g' hg').2.2.1 (hoff g' hg').2.2.2]; exact hwindows g' (by simp [hg']))
      (by simp only [M,Function.update_of_ne ‹src ≠ dst›,Function.update_self,tail])
      (by simp only [M,Function.update_self])
      (by
        intro i hi
        have ho : i ≠ src ∧ i ≠ dst := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl
          all_goals constructor <;> first | assumption | (apply Ne.symm; assumption)
        rw [hstable _ ho.1 ho.2]
        exact hclean i hi)
    refine ⟨v₂,hu₂.trans hu₁,?_⟩
    have he := Exec.seq he₁ he₂
    simpa [corePublicationGroupsProgram,corePublicationGroupsCost,corePublicationGroupsOutput,
      windows,M,E₁,CorePublicationClass.output,Function.update_comm ‹src ≠ dst›.symm,Function.update_idem,‹src ≠ dst›.symm,Nat.add_assoc] using he

theorem corePublicationGroups_native
    (control window : CorePublicationClass s width → Fin T)
    (savedControl gap src dst acc trash tmp : Fin T) (gs : List (CorePublicationClass s width)) :
    mnNativePushBound 2 (corePublicationGroupsProgram (P := P) (Q := Q) (A := A) (U := U)
      control window savedControl gap src dst acc trash tmp gs) := by
  have hp (g : CorePublicationClass s width) : mnNativePushBound 2
      (scatterBatch (P := P) (Q := Q) (A := A) (U := U) (control g) savedControl gap (window g) src dst acc trash tmp) := by
    simp [scatterBatch,scatterLoopBody,scatterPacket,gatherRead,gatherReadStep,WordCmd.peekRp,
      discardPrefix,transfer,moveR,uclear,keepIn,scanR,transferAct,drainR,popDo,whileR,
      moveStep,peekR,popPush,mnNativePushBound,mnActPush]
  induction gs with
  | nil => simp [corePublicationGroupsProgram,mnNativePushBound,mnActPush]
  | cons g gs ih => exact ⟨hp g,ih⟩

/-- Native stream work has a volume-based bound on every intermediate store.
The actual execution above supplies the premise; control preparation is separate. -/
theorem corePublicationGroups_within {body : P → Pr P T Q A U}
    {control window : CorePublicationClass s width → Fin T}
    {savedControl gap src dst acc trash tmp : Fin T} {gs : List (CorePublicationClass s width)}
    {v v' : HS T Q A U} {S F : Stacks T A} {w : ℕ} {hw : 0 < width}
    (he : Exec body (corePublicationGroupsProgram control window savedControl gap src dst acc trash tmp gs)
      (mk v S) (corePublicationGroupsCost w hw gs+1) (mk v' F)) (hw1 : 1 ≤ w) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(gs.length*(35*s*w+6)+1)) depth
      (corePublicationGroupsProgram control window savedControl gap src dst acc trash tmp gs)
      (mk v S) (corePublicationGroupsCost w hw gs+1) (mk v' F) := by
  have hb := corePublicationGroupsCost_le w hw gs hw1
  exact mn_native_exec_within he 2 (corePublicationGroups_native _ _ _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
