module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBulkLocalRowSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBulkSelectionCounts

/-! Run the ordinary-header bulk selector from retained replica, span and word
rulers. Its private clock and byte-volume ruler are generated and retired. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs
noncomputable section
variable {Q A s t : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

def selectionCountsState (N span w : ℕ) (S : Stacks tapes A) : Stacks tapes A :=
  {S with R := (Function.update (Function.update S.R (batch 0) (List.replicate N tick))
    (batch 1) (List.replicate (span*w) tick))}

theorem selectionCounts_regs :
    [plan.replicas,batch 5,plan.packet,batch 0,batch 1,scratch 2,scratch 3].Nodup := by
  simp [plan,RecoveryBanks.plan,recovery,batch,scratch,port_injective.eq_iff]

def countedBulkSelection : Pr P tapes Q A U :=
  .seq (bulkSelectionCounts plan.replicas (batch 5) plan.packet (batch 0) (batch 1) (scratch 2) (scratch 3))
    (.seq preparedBulkSelection (uclear (batch 1)))

def countedBulkSelectionCost (W V span w n N : ℕ) : ℕ :=
  bulkSelectionCountsCost N span w+(preparedBulkSelectionCost W V span w n N+(2*(span*w)+2))

theorem countedBulkSelection_native :
    mnNativePushBound 3 (countedBulkSelection (P := P) (Q := Q) (A := A) (U := U)) := by
  exact ⟨mnNativePushBound_mono (by decide) (bulkSelectionCounts_native ..),preparedBulkSelection_native,by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]⟩

theorem countedBulkSelection_exec {W V a origin span w n : ℕ}
    (hn : 0 < n) (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (Fs : List (ZMod t → GaussianInt)) (tail : List (Fin (A+4)))
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hheaders : LocalSelectionHeaders A W V s t a origin w n (embStk geometry S))
    (hspanRuler : (S.R (batch 5)).length = span) (hpacket : (S.R plan.packet).length = w)
    (hqueue : S.R (batch 2) = (Fs.flatMap fun F => cstream A w (cyclicInterval origin span F))++tail)
    (harchive : S.R (batch 3) = []) (hacc : S.R (batch 4) = [])
    (hdst : S.R source = []) (hline : S.R (geometry 110) = [])
    (hblank : ∀ k ∈ [batch 0,batch 1,scratch 2,scratch 3], S.R k = [])
    {d : InverseMasterInput s} {r : RawRecoveryJob s} {offset rows : ℕ}
    {wl : List (Fin (A+4))} (hready : plan.CroppedReady crop d r Fs.length offset rows wl S) :
    ∃ (v' : HS tapes Q A U) (B : Stacks 117 A) (m : ℕ),
      let G := selectionCountsState Fs.length span w S
      let K := embOvr geometry B.get G
      let F := {K with R := (Function.update (Function.update (Function.update K.R (batch 0) []) source
        (selectedWindowPayload (s := s) A w a n origin span Fs)) (batch 1) [])}
      v'.user = v.user ∧ m ≤ countedBulkSelectionCost W V span w n Fs.length ∧
      Exec body countedBulkSelection (Host.mk v S) m (Host.mk v' F) ∧
      plan.CroppedReady crop d r Fs.length offset rows wl F ∧
      F.R source = selectedWindowPayload (s := s) A w a n origin span Fs ∧
      F.R rowCount = List.replicate n tick ∧ F.R (batch 2) = S.R (batch 2) ∧
      (∀ i, F.R (recovery i) = S.R (recovery i)) ∧ (∀ i, F.R (scratch i) = S.R (scratch i)) ∧
      (∀ i ∈ [(0 : Fin 6),1], F.R (batch i) = []) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        3*countedBulkSelectionCost W V span w n Fs.length) depth countedBulkSelection (Host.mk v S) m (Host.mk v' F) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,_⟩ := bulkSelectionCounts_exec (body := body)
    plan.replicas (batch 5) plan.packet (batch 0) (batch 1) (scratch 2) (scratch 3)
    selectionCounts_regs Fs.length span w v S hready.replicas hspanRuler hpacket hblank
  let G := selectionCountsState Fs.length span w S
  have hg (i : Fin 117) : G.R (geometry i) = S.R (geometry i) := by
    simp only [selectionCountsState,G,Function.update_of_ne (geometry_ne_batch i 1),
      Function.update_of_ne (geometry_ne_batch i 0)]
  have hb (i : Fin 6) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : G.R (batch i) = S.R (batch i) := by
    simp [G,selectionCountsState,batch_injective.eq_iff,hi0,hi1]
  have hs (i : Fin 4) : G.R (scratch i) = S.R (scratch i) := by
    simp only [G,selectionCountsState,Function.update_of_ne (scratch_ne_batch i 1),
      Function.update_of_ne (scratch_ne_batch i 0)]
  have hr (i : RecoveryBank) : G.R (recovery i) = S.R (recovery i) := by
    simp only [G,selectionCountsState,Function.update_of_ne (batch_ne_recovery 1 i).symm,
      Function.update_of_ne (batch_ne_recovery 0 i).symm]
  have hproject : embStk geometry G = embStk geometry S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i; exact hg i
  have hreadyG : plan.CroppedReady crop d r Fs.length offset rows wl G := by
    apply hready.of_frame
    · intro k hk; obtain ⟨i,rfl⟩ := cropSupport_range k hk; exact hr i
    · intro i; rfl
  obtain ⟨v₂,B,m₂,hu₂,hm₂,he₂,hr₂,hrows₂,hqueue₂,hrecovery₂,hscratch₂,_⟩ :=
    preparedBulkSelection_exec (body := body) hn hwide hwindow hwV hspan hvol hVW hA hVpos Fs tail v₁ G
      (by rw [hproject]; exact hheaders)
      (by simp [G,selectionCountsState,batch_injective.eq_iff])
      (by simp [G,selectionCountsState])
      (by rw [hb 2 (by decide) (by decide)]; exact hqueue)
      (by rw [hb 3 (by decide) (by decide)]; exact harchive)
      (by rw [hb 4 (by decide) (by decide)]; exact hacc)
      (by exact (hg 108).trans hdst) (by rw [hg 110]; exact hline) hreadyG
  let K := embOvr geometry B.get G
  let H : Stacks tapes A := {K with R := (Function.update (Function.update K.R (batch 0) []) source
    (selectedWindowPayload (s := s) A w a n origin span Fs))}
  have hvolume : (H.R (batch 1)).length = span*w := by
    dsimp only [H,source]
    rw [Function.update_of_ne (geometry_ne_batch 108 1).symm,
      Function.update_of_ne (show batch 1 ≠ batch 0 by simp [batch_injective.eq_iff])]
    change ((embOvr geometry B.get G).R (batch 1)).length = _
    rw [(embOvr_off B.get G (fun j => geometry_ne_batch j 1)).2]
    simp [G,selectionCountsState]
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) (batch 1) v₂ H
  rw [hvolume] at he₃
  have hm : m₁+(m₂+(2*(span*w)+2)) ≤ countedBulkSelectionCost W V span w n Fs.length :=
    Nat.add_le_add hm₁ (Nat.add_le_add_right hm₂ _)
  have hex := Exec.seq he₁ (Exec.seq he₂ he₃)
  have hoff (k : Fin tapes) (hk : k ≠ batch 1) :
      ({H with R := Function.update H.R (batch 1) []} : Stacks tapes A).R k = H.R k :=
    Function.update_of_ne hk _ _
  refine ⟨v₃,B,_,hu₃.trans (hu₂.trans hu₁),hm,hex,?_,?_,?_,?_,?_,?_,?_,fun depth => ?_⟩
  · apply hr₂.of_frame
    · intro k hk
      obtain ⟨i,rfl⟩ := cropSupport_range k hk
      exact hoff _ (batch_ne_recovery 1 i).symm
    · intro i; rfl
  · rw [hoff source (geometry_ne_batch 108 1)]
    simp [H]
  · rw [hoff rowCount (geometry_ne_batch 116 1)]
    exact hrows₂
  · rw [hoff (batch 2) (by simp [batch_injective.eq_iff]),hqueue₂,hb 2 (by decide) (by decide)]
  · intro i; rw [hoff _ (batch_ne_recovery 1 i).symm,hrecovery₂,hr]
  · intro i; rw [hoff _ (scratch_ne_batch i 1),hscratch₂,hs]
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · rw [hoff (batch 0) (by simp [batch_injective.eq_iff])]
      simp [H,source,(geometry_ne_batch 108 0).symm]
    · exact Function.update_self _ _ _
  · exact mn_native_exec_within hex 3 countedBulkSelection_native depth _ (by omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
