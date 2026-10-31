module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationGroups

/-! Actual prepared publication of a finite class list, including padding
retirement and per-class control cleanup. Readiness is derived from the exact
shared-port frame; it is never supplied at an intermediate state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A s width : ℕ} {P U : Type} {src dst : Fin T}

def preparedPublicationGroupsProgram
    (plans : CorePublicationClass s width → PreparedPublicationPlan T src dst) :
    List (CorePublicationClass s width) → Pr P T Q A U
  | [] => .act .done
  | g::gs => .seq (plans g).program (preparedPublicationGroupsProgram plans gs)

def preparedPublicationGroupsCost (w : ℕ) (missing : CorePublicationClass s width → ℕ)
    (gs : List (CorePublicationClass s width)) : ℕ :=
  (gs.map (fun g => retireCountedLineCost (missing g*g.length) w+72*s*w+31)).sum+1

theorem preparedPublicationGroups_exec (body : P → Pr P T Q A U)
    (plans : CorePublicationClass s width → PreparedPublicationPlan T src dst)
    (gs : List (CorePublicationClass s width)) (w : ℕ) (hw : 0 < width) (hw1 : 1 ≤ w)
    (rows : CorePublicationClass s width → ℕ → List GaussianInt)
    (padded : CorePublicationClass s width → List (List GaussianInt))
    (missing : CorePublicationClass s width → ℕ)
    (borrowed : CorePublicationClass s width → List (Fin (A+4)))
    (hrows : ∀ g ∈ gs, ∀ k ∈ g.indices, (rows g k).length = g.length)
    (hpadded : ∀ g ∈ gs, ∀ row ∈ padded g, row.length = g.length)
    (hcount : ∀ g ∈ gs, missing g+g.indices.length = (padded g).length)
    (hreal : ∀ g ∈ gs, (padded g).flatten.drop (missing g*g.length) = (g.indices.map (rows g)).flatten)
    (E sourceTail outputTail : List (Fin (A+4))) (hE : E.length = s*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hready : ∀ g ∈ gs, (plans g).Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      w (missing g) (borrowed g) S)
    (hsrc : S.R src = gs.flatMap (fun g => cstream A w (padded g).flatten)++sourceTail)
    (hdst : S.R dst = E++outputTail) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedPublicationGroupsCost w missing gs ∧
      Exec body (preparedPublicationGroupsProgram plans gs) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail) dst
          (corePublicationGroupsOutput w hw rows gs E++outputTail))}) := by
  induction gs generalizing v S E with
  | nil =>
    have hs : S.R src = sourceTail := by simpa using hsrc
    refine ⟨v,1,rfl,by simp [preparedPublicationGroupsCost],?_⟩
    simpa only [preparedPublicationGroupsProgram,corePublicationGroupsOutput,←hs,Function.update_eq_self,
      ←hdst,Action.run] using Exec.act (body := body) (.done : Act T Q A U) (mk v S)
  | cons g gs ih =>
    let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
    let tail := gs.flatMap (fun g => cstream A w (padded g).flatten)++sourceTail
    have hl : ∀ row ∈ g.indices.map (rows g), row.length = g.length := by
      intro row hr
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
      exact hrows g (by simp) k hk
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := (plans g).exec body windows w (missing g) hw1 (padded g) (g.indices.map (rows g))
      (by simp [windows,coreSubsetPublicationWindows,PublicationWindows.restrict]) hl (hpadded g (by simp))
      (by simpa only [List.length_map] using hcount g (by simp)) (hreal g (by simp))
      E tail outputTail (borrowed g) hE v S (hready g (by simp))
      (by simpa only [List.flatMap_cons,List.append_assoc,tail] using hsrc) hdst
    let E₁ := g.output w hw (rows g) E
    let M : Stacks T A := {S with R := Function.update (Function.update S.R src tail) dst (E₁++outputTail)}
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih (fun g hg => hrows g (by simp [hg]))
      (fun g hg => hpadded g (by simp [hg])) (fun g hg => hcount g (by simp [hg]))
      (fun g hg => hreal g (by simp [hg])) E₁ (g.output_length w hw (rows g) (hrows g (by simp)) E hE) v₁ M
      (fun g hg => (hready g (by simp [hg])).after_io _ _)
      (by simp [M,(plans g).src_ne_dst,tail]) (by simp [M])
    refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,?_⟩
    · simp only [preparedPublicationGroupsCost,List.map_cons,List.sum_cons] at hn₂ ⊢
      omega
    · have he := Exec.seq he₁ he₂
      simpa [preparedPublicationGroupsProgram,corePublicationGroupsOutput,windows,M,E₁,CorePublicationClass.output,
        Function.update_comm (plans g).src_ne_dst.symm,Function.update_idem] using he

theorem preparedPublicationGroups_native
    (plans : CorePublicationClass s width → PreparedPublicationPlan T src dst)
    (gs : List (CorePublicationClass s width)) :
    mnNativePushBound 2 (preparedPublicationGroupsProgram (P := P) (Q := Q) (A := A) (U := U) plans gs) := by
  have hp (g : CorePublicationClass s width) : mnNativePushBound 2 ((plans g).program (P := P) (Q := Q) (A := A) (U := U)) :=
    preparedWindowPublication_native (plans g).count (plans g).savedControl (plans g).advances (plans g).savedAdvances
      (plans g).counter (plans g).window (plans g).zero (plans g).acc (plans g).control (plans g).trash (plans g).tmp
      (plans g).padRows (plans g).wordWidth (plans g).retireCount (plans g).gap src dst
  induction gs with
  | nil => simp [preparedPublicationGroupsProgram,mnNativePushBound,mnActPush]
  | cons g gs ih => exact ⟨hp g,ih⟩

theorem preparedPublicationGroups_within {body : P → Pr P T Q A U}
    {plans : CorePublicationClass s width → PreparedPublicationPlan T src dst}
    {gs : List (CorePublicationClass s width)} {missing : CorePublicationClass s width → ℕ}
    {w n : ℕ} {v v' : HS T Q A U} {S F : Stacks T A}
    (he : Exec body (preparedPublicationGroupsProgram plans gs) (mk v S) n (mk v' F))
    (hn : n ≤ preparedPublicationGroupsCost w missing gs) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*preparedPublicationGroupsCost w missing gs) depth
      (preparedPublicationGroupsProgram plans gs) (mk v S) n (mk v' F) := by
  exact mn_native_exec_within he 2 (preparedPublicationGroups_native plans gs) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
