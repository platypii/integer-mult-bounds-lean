module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedDiagonalBatch

/-! Retire the five shared allocations after the diagonal traversal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalSharedRoles : List RsbR := [.df,.cm .wn,.cm .pn,.cm .nn]
def diagonalSharedRegs : List (Fin tapes) := diagonalBytes::diagonalSharedRoles.map diagonalRole

def diagonalBatchLiveState (S : Stacks tapes A) (p w N n : ℕ)
    (page tail output : List (Fin (A+4))) : Stacks tapes A :=
  let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
  let M : Stacks tapes A := {E with R := diagonalCounterR p w E.R}
  diagonalBatchOutputState (diagonalBatchCounterState M N n w) tail output

theorem diagonalSharedRegs_nodup : diagonalSharedRegs.Nodup := by
  have hroles : diagonalSharedRoles.Nodup := by decide
  refine List.nodup_cons.mpr ⟨?_,hroles.map diagonalRole_injective⟩
  intro h
  obtain ⟨r,_,hr⟩ := List.mem_map.mp h
  exact diagonalRole_ne_work r 301 (by decide) hr

def retireDiagonalBatch : Pr P tapes Q A U := clearWords diagonalSharedRegs

theorem diagonalSharedRegs_blank (S : Stacks tapes A) (h : DiagonalFresh S) :
    ∀ k ∈ diagonalSharedRegs, S.R k = [] := by
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact h.work 301
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hk
    exact h.role r

theorem diagonalSharedRegs_off (k : Fin tapes) (hk : k ∈ diagonalSharedRegs) :
    k ≠ diagonalQueue ∧ k ≠ diagonalRole .dst := by
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨diagonalWork_ne_queue 301,(diagonalRole_ne_work .dst 301 (by decide)).symm⟩
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
    refine ⟨diagonalRole_ne_queue r,fun h => ?_⟩
    have hh := diagonalRole_injective h
    subst r
    simp [diagonalSharedRoles] at hr

theorem diagonalBatch_retirement_eq (S : Stacks tapes A) (p w N n : ℕ)
    (page tail output : List (Fin (A+4))) (hfresh : DiagonalFresh S) :
    let F := diagonalBatchLiveState S p w N n page tail output
    {F with R := fun k => if k ∈ diagonalSharedRegs then [] else F.R k} =
      {S with R := (Function.update (Function.update S.R diagonalQueue tail)
        (diagonalRole .dst) (output++S.R (diagonalRole .dst)))} := by
  dsimp only
  let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
  let M : Stacks tapes A := {E with R := diagonalCounterR p w E.R}
  let F := diagonalBatchLiveState S p w N n page tail output
  have hcounter (k : Fin tapes) (hw : k ≠ diagonalCr .wn) (hp : k ≠ diagonalCr .pn)
      (hn : k ≠ diagonalCr .nn) (hd : k ≠ diagonalRole .df) : M.R k = S.R k :=
    (chirpMultiplierSetup_off diagonalCr E.R p w k hw hp hn).trans (Function.update_of_ne hd _ _)
  have hdst : M.R (diagonalRole .dst) = S.R (diagonalRole .dst) :=
    (diagonalCounter_role_off p w E.R .dst (by simp) (by simp) (by simp)).trans
      (Function.update_of_ne (diagonalRole_injective.ne (by decide : RsbR.dst ≠ .df)) _ _)
  have hdc : diagonalRole .dst ≠ diagonalClock := diagonalRole_ne_work .dst 300 (by decide)
  have hdb : diagonalRole .dst ≠ diagonalBytes := diagonalRole_ne_work .dst 301 (by decide)
  refine Stacks.ext (show F.inp = S.inp from rfl) (show F.out = S.out from rfl)
    (show F.L = S.L from rfl) ?_
  funext k
  change (if k ∈ diagonalSharedRegs then [] else F.R k) = _
  by_cases hk : k ∈ diagonalSharedRegs
  · rw [ite_eq_left hk]
    have hoff := diagonalSharedRegs_off k hk
    exact ((Function.update_of_ne hoff.2 _ _).trans
      ((Function.update_of_ne hoff.1 _ _).trans (diagonalSharedRegs_blank S hfresh k hk))).symm
  · rw [ite_eq_right hk]
    by_cases hd : k = diagonalRole .dst
    · subst k
      simp only [F,diagonalBatchLiveState,diagonalBatchOutputState,Function.update_self]
      exact congrArg (fun xs => output++xs)
        ((Function.update_of_ne hdb _ _).trans ((Function.update_of_ne hdc _ _).trans hdst))
    · by_cases hq : k = diagonalQueue
      · subst k
        simp only [F,diagonalBatchLiveState,diagonalBatchOutputState,Function.update_of_ne hd,Function.update_self]
      · by_cases hc : k = diagonalClock
        · subst k
          change Function.update (Function.update (Function.update
            (diagonalBatchCounterState M N n w).R diagonalClock []) diagonalQueue tail)
            (diagonalRole .dst) _ diagonalClock = _
          simp only [Function.update_of_ne hd,Function.update_of_ne hq,Function.update_self]
          exact (hfresh.work 300).symm
        · have hnot (r : RsbR) (hr : r ∈ diagonalSharedRoles) : k ≠ diagonalRole r := by
            intro he
            exact hk (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,he.symm⟩))
          have hb : k ≠ diagonalBytes := fun h => hk (List.mem_cons.mpr (Or.inl h))
          have hmk := hcounter k (hnot (.cm .wn) (by simp [diagonalSharedRoles]))
            (hnot (.cm .pn) (by simp [diagonalSharedRoles])) (hnot (.cm .nn) (by simp [diagonalSharedRoles]))
            (hnot .df (by simp [diagonalSharedRoles]))
          change Function.update (Function.update (Function.update
            (Function.update (Function.update M.R diagonalClock _) diagonalBytes _) diagonalClock [])
              diagonalQueue tail) (diagonalRole .dst) _ k = _
          simp only [Function.update_of_ne hd,Function.update_of_ne hq,Function.update_of_ne hc,Function.update_of_ne hb]
          exact hmk

theorem retireDiagonalBatch_native :
    mnNativePushBound 0 (retireDiagonalBatch (P := P) (Q := Q) (A := A) (U := U)) :=
  clearWords_native _

def retireDiagonalBatchCost (F : Stacks tapes A) : ℕ :=
  2*(diagonalSharedRegs.map (fun k => (F.R k).length)).sum+11

theorem retireDiagonalBatchCost_eq (S : Stacks tapes A) (p w N n : ℕ)
    (page tail output : List (Fin (A+4))) (hfresh : DiagonalFresh S) :
    retireDiagonalBatchCost (diagonalBatchLiveState S p w N n page tail output) =
      2*(n*w+page.length+w+p+IntegerMultBounds.Schoenhage.Schedule.topN w)+11 := by
  let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
  let M : Stacks tapes A := {E with R := diagonalCounterR p w E.R}
  let F := diagonalBatchLiveState S p w N n page tail output
  have hrole (r : RsbR) (hr : r ≠ .dst) : F.R (diagonalRole r) = M.R (diagonalRole r) := by
    have hd : diagonalRole r ≠ diagonalRole .dst := diagonalRole_injective.ne hr
    have hq := diagonalRole_ne_queue r
    have hc : diagonalRole r ≠ diagonalClock := diagonalRole_ne_work r 300 (by decide)
    have hb : diagonalRole r ≠ diagonalBytes := diagonalRole_ne_work r 301 (by decide)
    change Function.update (Function.update (Function.update
      (Function.update (Function.update M.R diagonalClock _) diagonalBytes _) diagonalClock [])
        diagonalQueue tail) (diagonalRole .dst) _ (diagonalRole r) = _
    simp only [Function.update_of_ne hd,Function.update_of_ne hq,Function.update_of_ne hc,Function.update_of_ne hb]
  have hready : RsbReady (fun r => M.R (diagonalRole r)) w p := by
    apply diagonalCounter_ready
    intro c
    have hne : diagonalCr c ≠ diagonalRole .df := by intro h; cases diagonalRole_injective h
    exact (Function.update_of_ne hne _ _).trans (hfresh.role (.cm c))
  have hwn : (F.R (diagonalRole (.cm .wn))).length = w :=
    (congrArg List.length (hrole _ (by decide))).trans hready.wn
  have hpn : (F.R (diagonalRole (.cm .pn))).length = p :=
    (congrArg List.length (hrole _ (by decide))).trans hready.pn
  have hnn : (F.R (diagonalRole (.cm .nn))).length = IntegerMultBounds.Schoenhage.Schedule.topN w :=
    (congrArg List.length (hrole _ (by decide))).trans hready.nn
  have hpage : (F.R (diagonalRole .df)).length = page.length :=
    congrArg List.length ((hrole .df (by decide)).trans
      (diagonalPage_multiplier_frame p w S hfresh page).2.1)
  have hbytes : (F.R diagonalBytes).length = n*w := by
    have hd : diagonalBytes ≠ diagonalRole .dst := (diagonalRole_ne_work .dst 301 (by decide)).symm
    have hq : diagonalBytes ≠ diagonalQueue := diagonalWork_ne_queue 301
    have hc : diagonalBytes ≠ diagonalClock := by simp [diagonalBytes,diagonalClock,recovery_injective.eq_iff]
    change (Function.update (Function.update (Function.update
      (Function.update (Function.update M.R diagonalClock _) diagonalBytes (List.replicate (n*w) tick))
        diagonalClock []) diagonalQueue tail) (diagonalRole .dst) _ diagonalBytes).length = _
    simp only [Function.update_of_ne hd,Function.update_of_ne hq,Function.update_of_ne hc,
      Function.update_self,List.length_replicate]
  change 2*(diagonalSharedRegs.map (fun k => (F.R k).length)).sum+11 = _
  simp only [diagonalSharedRegs,diagonalSharedRoles,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    hbytes,hpage,hwn,hpn,hnn]
  omega

theorem retireDiagonalBatch_exec (S : Stacks tapes A) (p w N n : ℕ)
    (page tail output : List (Fin (A+4))) (hfresh : DiagonalFresh S)
    (v : HS tapes Q A U) :
    let F := diagonalBatchLiveState S p w N n page tail output
    ∃ v', v'.user = v.user ∧ ∀ depth,
      ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v F)+depth+0) depth retireDiagonalBatch
        (mk v F) (retireDiagonalBatchCost F)
        (mk v' {S with R := (Function.update (Function.update S.R diagonalQueue tail)
          (diagonalRole .dst) (output++S.R (diagonalRole .dst)))}) := by
  dsimp only
  let F := diagonalBatchLiveState S p w N n page tail output
  obtain ⟨v',hv,he⟩ := clearWords_exec (body := body) diagonalSharedRegs diagonalSharedRegs_nodup v F
  have hex : Exec body retireDiagonalBatch (mk v F) (retireDiagonalBatchCost F)
      (mk v' {S with R := (Function.update (Function.update S.R diagonalQueue tail)
        (diagonalRole .dst) (output++S.R (diagonalRole .dst)))}) :=
    he.cast (by simp [retireDiagonalBatchCost,diagonalSharedRegs,diagonalSharedRoles])
      (congrArg (mk v') (diagonalBatch_retirement_eq S p w N n page tail output hfresh))
  exact ⟨v',hv,fun depth => mn_native_exec_within hex 0 retireDiagonalBatch_native depth
    (mnSize (mk v F)+depth+0) (by omega)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
