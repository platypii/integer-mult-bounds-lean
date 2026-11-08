module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryHandoff
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRecoveryLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalSelectionHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicLocalRowSelection

/-! Execute the ordinary-header selector in the concrete recovery caller.
Its actual output and retained row ruler occupy the generated handoff ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  ScalarPlacement

namespace ScalarPlacement.LocalRecoveryLayout
noncomputable section
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

def selection : Pr P tapes Q A U :=
  embProg geometry Empty.elim (preparedLocalRowSelection (P := Empty))

theorem selection_exec {W V t a origin span w n : ℕ}
    (hn : 0 < n) (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (F : ZMod t → GaussianInt) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hheaders : LocalSelectionHeaders A W V s t a origin w n (embStk geometry S))
    (hsrc : S.R (geometry 110) = cstream A w (cyclicInterval origin span F))
    {d : InverseMasterInput s} {r : RawRecoveryJob s} {N offset rows : ℕ}
    {wl : List (Fin (A+4))} (hready : plan.CroppedReady crop d r N offset rows wl S) :
    ∃ (v' : HS tapes Q A U) (B : Stacks 117 A) (m : ℕ), v'.user = v.user ∧
      m ≤ (110*W+4*V+137)+(localRowControlsCost W V span w n+n*(14*w+25)+12*(span*w)+6*w+38) ∧
      Exec body selection (Host.mk v S) m (Host.mk v' (embOvr geometry B.get S)) ∧
      plan.CroppedReady crop d r N offset rows wl (embOvr geometry B.get S) ∧
      (embOvr geometry B.get S).R source =
        cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))++S.R source ∧
      (embOvr geometry B.get S).R rowCount = List.replicate n tick := by
  obtain ⟨v₁,B,m,hu₁,hm,he,_,_,_,hout,_,_,hcount,_⟩ :=
    preparedCyclicLocalRowSelection_exec (P := Empty) (body := fun z => nomatch z)
      hn hwide hwindow hwV hspan hvol hVW hA hVpos F (embDn geometry v) (embStk geometry S)
      hheaders.width hheaders.movementWidth hheaders.sourceSize hheaders.targetSize
      hheaders.sourceOrigin hheaders.targetOrigin hheaders.rowCount hheaders.zero hheaders.table
      hheaders.word hheaders.zero104 hheaders.zero106 hheaders.zero116 hheaders.fresh
      hsrc hheaders.row hheaders.control hheaders.clean
  obtain ⟨v₂,_,hu₂,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) geometry_injective
    (fun z => nomatch z) he v rfl S rfl
  have hread := embStk_ovr geometry_injective B S
  refine ⟨v₂,B,m,hu₂.trans hu₁,hm,he₂,ready_geometry_ovr hready B,?_,?_⟩
  · have h := congrArg (fun K : Stacks 117 A => K.R 108) hread
    exact h.trans hout
  · have h := congrArg (fun K : Stacks 117 A => K.R 116) hread
    exact h.trans hcount

def selectionHandoff : Pr P tapes Q A U :=
  .seq selection (generatedTakePrefix plan.replicas rowCount plan.packet (scratch 0) (scratch 1)
    source (plan.work 124) (scratch 2) (scratch 3))

/-- Execute selection and transfer its actual output into the recovery bank.
The pre-existing output suffix is borrowed and restored without inspection. -/
theorem selection_handoff_exec {W V t a origin span w n : ℕ}
    (hn : 0 < n) (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (F : ZMod t → GaussianInt) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hheaders : LocalSelectionHeaders A W V s t a origin w n (embStk geometry S))
    (hsrc : S.R (geometry 110) = cstream A w (cyclicInterval origin span F))
    {d : InverseMasterInput s} {r : RawRecoveryJob s} {offset rows : ℕ}
    {wl : List (Fin (A+4))} (hready : plan.CroppedReady crop d r 1 offset rows wl S)
    (hjobSpan : n = r.problem.span) (hjobWidth : w = r.W)
    (hinput : S.R (plan.work 124) = []) (hblank : ∀ i, S.R (scratch i) = []) :
    let payload := cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))
    ∃ (v' : HS tapes Q A U) (B : Stacks 117 A) (m : ℕ),
      let H := plan.inputState source payload (S.R source) (embOvr geometry B.get S)
      v'.user = v.user ∧
      m ≤ (110*W+4*V+137)+(localRowControlsCost W V span w n+n*(14*w+25)+12*(span*w)+6*w+38)+
        generatedTakePrefixCost 1 r.problem.span r.W ∧
      Exec body selectionHandoff (Host.mk v S) m (Host.mk v' H) ∧
      plan.CroppedReady crop d r 1 offset rows wl H ∧
      H.R (plan.work 124) = payload ∧ H.R source = S.R source := by
  dsimp only
  obtain ⟨v₁,B,m₁,hu₁,hm₁,he₁,hr₁,hout,hcount⟩ := selection_exec (body := body)
    hn hwide hwindow hwV hspan hvol hVW hA hVpos F v S hheaders hsrc hready
  let payload := cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))
  let K := embOvr geometry B.get S
  have hlen : payload.length = 1*(r.problem.span*r.W) := by
    simp [payload,length_cstream,hjobSpan,hjobWidth]
  have hwork : K.R (plan.work 124) = [] := by
    exact ((embOvr_off B.get S (fun j => geometry_ne_recovery j (.work 124))).2).trans hinput
  have hs (i : Fin 4) : K.R (scratch i) = [] := by
    exact ((embOvr_off B.get S (fun j => geometry_ne_scratch j i)).2).trans (hblank i)
  obtain ⟨v₂,m₂,hu₂,hm₂,hr₂,_,he₂,_⟩ := hr₁.generatedTakePrefix_exec (body := body)
    rowCount (scratch 0) (scratch 1) source (scratch 2) (scratch 3) handoff_regs
    (geometry_off_support 108) payload (S.R source) hlen v₁ hout
    (by rw [hcount,List.length_replicate,hjobSpan]) hwork
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> exact hs _)
  refine ⟨v₂,B,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂,hr₂,?_,?_⟩
  · simp [ComputedRecoveryPlan.inputState]
  · have hne : source ≠ plan.work 124 := geometry_ne_recovery 108 (.work 124)
    simp [ComputedRecoveryPlan.inputState,hne]


end
end ScalarPlacement.LocalRecoveryLayout
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
