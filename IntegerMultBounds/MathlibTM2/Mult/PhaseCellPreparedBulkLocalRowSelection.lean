module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBulkLocalRowSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareLocalRowControls
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! One ordinary-header controller preparation followed by the fixed replica
sweep. Numerical recovery readiness survives the complete selection program. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs
noncomputable section
variable {Q A s t : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

def preparedBulkSelection : Pr P tapes Q A U :=
  .seq (embProg geometry Empty.elim (prepareLocalRowControls (P := Empty))) bulkSelection

def preparedBulkSelectionCost (W V span w n N : ℕ) : ℕ :=
  (110*W+4*V+137)+localRowControlsCost W V span w n+restoringCyclicSelectionCost N n span w

theorem preparedBulkSelection_native :
    mnNativePushBound 3 (preparedBulkSelection (P := P) (Q := Q) (A := A) (U := U)) := by
  exact ⟨embProg_native _ _ _ prepareLocalRowControls_native,
    mnNativePushBound_mono (by decide) (restoringCyclicSelection_native ..)⟩

theorem preparedBulkSelection_exec {W V a origin span w n : ℕ}
    (hn : 0 < n) (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (Fs : List (ZMod t → GaussianInt)) (tail : List (Fin (A+4)))
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hheaders : LocalSelectionHeaders A W V s t a origin w n (embStk geometry S))
    (hclock : (S.R (batch 0)).length = Fs.length) (hvolume : (S.R (batch 1)).length = span*w)
    (hqueue : S.R (batch 2) = (Fs.flatMap fun F => cstream A w (cyclicInterval origin span F))++tail)
    (harchive : S.R (batch 3) = []) (hacc : S.R (batch 4) = [])
    (hdst : S.R source = []) (hline : S.R (geometry 110) = [])
    {d : InverseMasterInput s} {r : RawRecoveryJob s} {N offset rows : ℕ}
    {wl : List (Fin (A+4))} (hready : plan.CroppedReady crop d r N offset rows wl S) :
    ∃ (v' : HS tapes Q A U) (B : Stacks 117 A) (m : ℕ),
      let K := embOvr geometry B.get S
      let F := {K with R := (Function.update (Function.update K.R (batch 0) []) source
        (selectedWindowPayload (s := s) A w a n origin span Fs))}
      v'.user = v.user ∧ m ≤ preparedBulkSelectionCost W V span w n Fs.length ∧
      Exec body preparedBulkSelection (Host.mk v S) m (Host.mk v' F) ∧
      plan.CroppedReady crop d r N offset rows wl F ∧
      F.R rowCount = List.replicate n tick ∧ F.R (batch 2) = S.R (batch 2) ∧
      (∀ i, F.R (recovery i) = S.R (recovery i)) ∧
      (∀ i, F.R (scratch i) = S.R (scratch i)) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        3*preparedBulkSelectionCost W V span w n Fs.length) depth preparedBulkSelection (Host.mk v S) m (Host.mk v' F) := by
  obtain ⟨v₁,B,m₁,hu₁,hm₁,he₁,_,_,_,hR⟩ := prepareLocalRowControls_exec
    (P := Empty) (body := fun z => nomatch z) hn hwide hwindow hwV hspan hvol hVW hA hVpos
    (embDn geometry v) (embStk geometry S) hheaders
  obtain ⟨v₂,_,hu₂,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) geometry_injective
    (fun z => nomatch z) he₁ v rfl S rfl
  let K := embOvr geometry B.get S
  have hg (i : Fin 117) : K.R (geometry i) = B.R i :=
    congrArg (fun H : Stacks 117 A => H.R i) (embStk_ovr geometry_injective B S)
  have hb (i : Fin 6) : K.R (batch i) = S.R (batch i) :=
    (embOvr_off B.get S (fun j => geometry_ne_batch j i)).2
  have hoff (i : Fin 117) (h91 : i ≠ 91) (h109 : i ≠ 109) (h116 : i ≠ 116) :
      K.R (geometry i) = S.R (geometry i) := by
    rw [hg,hR]
    simp only [h91,h109,h116,ite_false]
    rfl
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃,hr₃,_⟩ := bulkSelection_exec (body := body)
    w a n origin span Fs hn hwindow tail v₂ K
    (by rw [hb]; exact hclock) (by rw [hb]; exact hvolume)
    (by rw [hg,hR]; simp)
    (by rw [hb]; exact hqueue)
    (by rw [hoff 103 (by decide) (by decide) (by decide)]; exact hheaders.row)
    (by rw [hoff 94 (by decide) (by decide) (by decide)]; exact hheaders.word)
    (by rw [hb]; exact harchive) (by rw [hb]; exact hacc)
    (by
      intro i hi
      have hne : i ≠ 91 ∧ i ≠ 109 ∧ i ≠ 116 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hoff i hne.1 hne.2.1 hne.2.2]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | hi
      · exact hdst
      · exact hline
      · exact hheaders.clean _ (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hi))
    (ready_geometry_ovr hready B)
  have hm : m₁+m₃ ≤ preparedBulkSelectionCost W V span w n Fs.length := Nat.add_le_add hm₁ hm₃
  have hex := Exec.seq he₂ he₃
  refine ⟨v₃,B,m₁+m₃,hu₃.trans (hu₂.trans hu₁),hm,hex,hr₃,?_,?_,?_,?_,fun depth => ?_⟩
  · change Function.update (Function.update K.R (batch 0) []) source
      (selectedWindowPayload (s := s) A w a n origin span Fs) (geometry 116) = _
    rw [Function.update_of_ne (show geometry 116 ≠ source by exact fun he => (by decide : (116 : Fin 117) ≠ 108) (geometry_injective he)),
      Function.update_of_ne (geometry_ne_batch 116 0),hg,hR]
    simp
  · dsimp only [source]
    simp only [Function.update_of_ne (geometry_ne_batch 108 2).symm,
      Function.update_of_ne (show batch 2 ≠ batch 0 by simp [batch_injective.eq_iff])]
    exact hb 2
  · intro i
    dsimp only [source]
    simp only [Function.update_of_ne (geometry_ne_recovery 108 i).symm,
      Function.update_of_ne (batch_ne_recovery 0 i).symm]
    exact (embOvr_off B.get S (fun j => geometry_ne_recovery j i)).2
  · intro i
    dsimp only [source]
    simp only [Function.update_of_ne (geometry_ne_scratch 108 i).symm,
      Function.update_of_ne (scratch_ne_batch i 0)]
    exact (embOvr_off B.get S (fun j => geometry_ne_scratch j i)).2
  · exact mn_native_exec_within hex 3 preparedBulkSelection_native depth _ (by omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
