module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedRetainedSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicCount
public import IntegerMultBounds.MathlibTM2.Host.EmbedLeftFrame
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackInvariantShift

/-! Place the existing selector beside the concrete cyclic caller, preserving
all external seeds and numerical tapes, and sharing its exact RHS endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs Routing.RetainedHaloTensor
noncomputable section
variable {ι : Type} [DecidableEq ι]
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

private theorem readPlacedR {M N A : ℕ} (e : Fin M → Fin N) (he : Function.Injective e)
    (B : Stacks M A) (S : Stacks N A) (j : Fin M) :
    (embOvr e B.get S).R (e j) = B.R j := embExt_apply he B.R S.R j

private theorem shiftStock {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    {p : Pr P T Q A U} {v vf : HS T Q A U} {S F : Stacks T A} {n budget : ℕ}
    (h : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+budget)
      0 p (mk v S) n (mk vf F)) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+budget)
      depth p (mk v S) n (mk vf F) := by
  simpa only [Nat.zero_add,Nat.add_zero,Nat.add_right_comm] using mn_exec_within_shift h depth

private theorem left_count_update {T A : ℕ} (S F : Stacks T A)
    (count : Fin T) (word : List (Fin (A+4))) (hleft : F.L = S.L) :
    ({F with R := Function.update F.R count word} : Stacks T A).L = S.L := hleft

private theorem frame_count_update {M T A : ℕ} (e : Fin M → Fin T)
    (S F : Stacks T A) (count : Fin T) (word : List (Fin (A+4)))
    (hframe : ∀ j, (∀ r, e r ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) :
    ∀ j, j ≠ count → (∀ r, e r ≠ j) →
      ({F with R := Function.update F.R count word} : Stacks T A).L j = S.L j ∧
      ({F with R := Function.update F.R count word} : Stacks T A).R j = S.R j := by
  intro j hj hoff
  exact ⟨(hframe j hoff).1,(Function.update_of_ne hj _ _).trans (hframe j hoff).2⟩

def selection : Pr P tapes Q A U :=
  embProg selector Empty.elim (LocalRecoveryLayout.preparedBulkSelection (P := Empty))

theorem selection_exec
    (axis : ι → Axis) (retained : Finset ι) (f : (ι → ℕ) → GaussianInt)
    (before middle : List (Sum ι ι)) (aPrefix : ℕ) (i : ι) (hi : i ∈ retained) (k : ℕ)
    (hH : (axis i).H ≤ (axis i).N*(axis i).L) (hguard : (axis i).H ≤ k*(axis i).L)
    {W V a w n : ℕ} (hsource : a+n ≤ s)
    (hn : 0 < n) (hwide : a+n+2*((axis i).N*(axis i).L)*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, (k*(axis i).L-(axis i).H) ≤ nearestNatural s ((axis i).N*(axis i).L) (a+j) ∧ nearestNatural s ((axis i).N*(axis i).L) (a+j) < (k*(axis i).L-(axis i).H)+((axis i).L+2*(axis i).H))
    (hwV : w < 2^V) (hspan : ((axis i).L+2*(axis i).H) < 2^V) (hvol : ((axis i).L+2*(axis i).H)*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (tail : List (Fin (A+4)))
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hheaders : LocalSelectionHeaders A W V s ((axis i).N*(axis i).L) a (k*(axis i).L-(axis i).H) w n (embStk LocalRecoveryLayout.geometry (embStk selector S)))
    (hclock : (S.R (selector (LocalRecoveryLayout.batch 0))).length = ((middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod)) (hvolume : (S.R (selector (LocalRecoveryLayout.batch 1))).length = ((axis i).L+2*(axis i).H)*w)
    (hqueue : S.R (selector (LocalRecoveryLayout.batch 2)) = Routing.RetainedFieldBatch.batch A w axis retained before middle i aPrefix k f++tail)
    (harchive : S.R (selector (LocalRecoveryLayout.batch 3)) = []) (hacc : S.R (selector (LocalRecoveryLayout.batch 4)) = [])
    (hdst : S.R caller.archive = []) (hline : S.R (geometry 110) = []) :
    let payload := cstream A w ((selectedRhsFields s
      ((Routing.RetainedFieldBatch.replicas axis retained before middle aPrefix).map
        (fun c => retainedTensorLine axis retained f c i))).map (packedInterval a n)).flatten
    ∃ (v' : HS tapes Q A U) (B : Stacks 117 A) (m : ℕ),
      let S₀ := embStk selector S
      let K := embOvr LocalRecoveryLayout.geometry B.get S₀
      let F₀ := {K with R := (Function.update (Function.update K.R (LocalRecoveryLayout.batch 0) [])
        LocalRecoveryLayout.source payload)}
      let F := embOvr selector F₀.get S
      v'.user = v.user ∧
      m ≤ LocalRecoveryLayout.preparedBulkSelectionCost W V ((axis i).L+2*(axis i).H) w n
        (middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod ∧
      Exec body selection (mk v S) m (mk v' F) ∧
      F.R caller.archive = payload ∧
      (F.R caller.archive).length = (middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod*n*w ∧
      F.R caller.span = List.replicate n tick ∧
      F.R (caller.controls 0) = S.R (caller.controls 0) ∧
      F.R (selector (LocalRecoveryLayout.batch 2)) = S.R (selector (LocalRecoveryLayout.batch 2)) ∧
      (∀ i, F.R (selector (LocalRecoveryLayout.recovery i)) = S.R (selector (LocalRecoveryLayout.recovery i))) ∧
      F.L = S.L ∧
      (∀ j, (∀ r, selector r ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        3*LocalRecoveryLayout.preparedBulkSelectionCost W V ((axis i).L+2*(axis i).H) w n
          (middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod)
        depth selection (mk v S) m (mk v' F) := by
  dsimp only
  let S₀ := embStk selector S
  obtain ⟨vi,B,m,hu,hm,he,hlen,hrows,hqueueFinal,hrecovery,hscratch,hleft,hscalarFrame,hwithin⟩ :=
    LocalRecoveryLayout.preparedRetainedSelection_exec (P := Empty) (body := fun z => nomatch z)
      axis retained f before middle aPrefix i hi k hH hguard hsource hn hwide hwindow hwV hspan hvol
      hVW hA hVpos tail (embDn selector v) S₀ hheaders hclock hvolume hqueue harchive hacc hdst hline
  let payload := cstream A w ((selectedRhsFields s
    ((Routing.RetainedFieldBatch.replicas axis retained before middle aPrefix).map
      (fun c => retainedTensorLine axis retained f c i))).map (packedInterval a n)).flatten
  let K := embOvr LocalRecoveryLayout.geometry B.get S₀
  let F₀ := {K with R := (Function.update (Function.update K.R (LocalRecoveryLayout.batch 0) [])
    LocalRecoveryLayout.source payload)}
  let F := embOvr selector F₀.get S
  obtain ⟨vf,hvf,huf,hex⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) selector_injective
    (fun z => nomatch z) he v rfl S rfl
  simp only [embDn_user] at hu
  have huser : vf.user = v.user := huf.trans hu
  have hread (j : Fin LocalRecoveryLayout.tapes) : F.R (selector j) = F₀.R j :=
    readPlacedR selector selector_injective F₀ S j
  refine ⟨vf,B,m,huser,hm,hex,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change F.R (selector LocalRecoveryLayout.source) = payload
    rw [hread]
    simp only [F₀,Function.update_self]
  · change (F.R (selector LocalRecoveryLayout.source)).length = _
    rw [hread]
    exact hlen
  · change F.R (selector LocalRecoveryLayout.rowCount) = _
    rw [hread]
    exact hrows
  · change F.R (selector (LocalRecoveryLayout.geometry 94)) =
      S.R (selector (LocalRecoveryLayout.geometry 94))
    rw [hread]
    have hne : LocalRecoveryLayout.geometry 94 ≠ LocalRecoveryLayout.source := by
      simp [LocalRecoveryLayout.source,LocalRecoveryLayout.geometry_injective.eq_iff]
    simp only [F₀,Function.update_of_ne hne,
      Function.update_of_ne (LocalRecoveryLayout.geometry_ne_batch 94 0)]
    have hg := congrArg (fun D : Stacks 117 A => D.R 94)
      (embStk_ovr LocalRecoveryLayout.geometry_injective B S₀)
    change K.R (LocalRecoveryLayout.geometry 94) = B.R 94 at hg
    rw [hg,hscalarFrame 94 (by decide) (by decide) (by decide)]
    rfl
  · rw [hread]
    exact hqueueFinal
  · intro i
    rw [hread]
    exact hrecovery i
  · exact embOvr_left_eq selector selector_injective F₀ S
      (embOvr_left_eq LocalRecoveryLayout.geometry LocalRecoveryLayout.geometry_injective B S₀ hleft)
  · intro j hj
    exact embOvr_off F₀.get S hj
  · intro depth
    exact exec_emb_within_stock_of_exec selector_injective (ι := Empty.elim) (body' := body)
      (fun z => nomatch z) (hwithin depth) v rfl S rfl hex

def selectionCount : Pr P tapes Q A U := .seq selection prepareCount

theorem selectionCount_exec
    (axis : ι → Axis) (retained : Finset ι) (f : (ι → ℕ) → GaussianInt)
    (before middle : List (Sum ι ι)) (aPrefix : ℕ) (i : ι) (hi : i ∈ retained) (k : ℕ)
    (hH : (axis i).H ≤ (axis i).N*(axis i).L) (hguard : (axis i).H ≤ k*(axis i).L)
    {W V a w n : ℕ} (hsource : a+n ≤ s)
    (hn : 0 < n) (hwide : a+n+2*((axis i).N*(axis i).L)*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, (k*(axis i).L-(axis i).H) ≤ nearestNatural s ((axis i).N*(axis i).L) (a+j) ∧ nearestNatural s ((axis i).N*(axis i).L) (a+j) < (k*(axis i).L-(axis i).H)+((axis i).L+2*(axis i).H))
    (hwV : w < 2^V) (hspan : ((axis i).L+2*(axis i).H) < 2^V) (hvol : ((axis i).L+2*(axis i).H)*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (tail : List (Fin (A+4)))
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hheaders : LocalSelectionHeaders A W V s ((axis i).N*(axis i).L) a (k*(axis i).L-(axis i).H) w n (embStk LocalRecoveryLayout.geometry (embStk selector S)))
    (hclock : (S.R (selector (LocalRecoveryLayout.batch 0))).length = ((middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod)) (hvolume : (S.R (selector (LocalRecoveryLayout.batch 1))).length = ((axis i).L+2*(axis i).H)*w)
    (hqueue : S.R (selector (LocalRecoveryLayout.batch 2)) = Routing.RetainedFieldBatch.batch A w axis retained before middle i aPrefix k f++tail)
    (harchive : S.R (selector (LocalRecoveryLayout.batch 3)) = []) (hacc : S.R (selector (LocalRecoveryLayout.batch 4)) = [])
    (hdst : S.R caller.archive = []) (hline : S.R (geometry 110) = [])
    (hN : (S.R (aux 7)).length = (middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod)
    (hcountBlank : ∀ j ∈ [aux 6,caller.count,caller.saved,caller.tmp], S.R j = []) :
    let N := (middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod
    ∃ (v' : HS tapes Q A U) (C : Stacks tapes A) (m : ℕ),
      v'.user = v.user ∧
      m ≤ LocalRecoveryLayout.preparedBulkSelectionCost W V ((axis i).L+2*(axis i).H) w n N+
        (archiveWidthSetupCost N n w+2*(n*w)+3) ∧
      Exec body selectionCount (mk v S) m (mk v' C) ∧
      SelectedInput (selectedRhsFields s
        ((Routing.RetainedFieldBatch.replicas axis retained before middle aPrefix).map
          (fun c => retainedTensorLine axis retained f c i))) a n w S C ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*LocalRecoveryLayout.preparedBulkSelectionCost W V ((axis i).L+2*(axis i).H) w n N+
          2*archiveWidthSetupCost N n w)) depth selectionCount (mk v S) m (mk v' C) := by
  dsimp only
  obtain ⟨vi,B,m,hu,hm,he,hsrc,hlen,hrows,hwidth,hqueueRestored,hrecovery,hleft,hframe,hwithin⟩ := selection_exec (body := body)
    axis retained f before middle aPrefix i hi k hH hguard hsource hn hwide hwindow hwV hspan hvol
    hVW hA hVpos tail v S hheaders hclock hvolume hqueue harchive hacc hdst hline
  let payload := cstream A w ((selectedRhsFields s
    ((Routing.RetainedFieldBatch.replicas axis retained before middle aPrefix).map
      (fun c => retainedTensorLine axis retained f c i))).map (packedInterval a n)).flatten
  let K := embOvr LocalRecoveryLayout.geometry B.get (embStk selector S)
  let F₀ := {K with R := (Function.update (Function.update K.R (LocalRecoveryLayout.batch 0) [])
    LocalRecoveryLayout.source payload)}
  let F := embOvr selector F₀.get S
  let N := (middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod
  have haux (j : Fin 8) : F.R (aux j) = S.R (aux j) :=
    (hframe _ (fun r => selector_ne_aux r j)).2
  obtain ⟨vf,l,huf,hl,hcount⟩ := prepareCount_exec (body := body) N n w 0 vi F
    (by rw [haux]; exact hN) (by rw [hrows]; simp)
    (by rw [hwidth]; exact hheaders.word)
    (by intro j hj
        change j ∈ [aux 6,aux 2,aux 3,aux 4] at hj
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl
        all_goals rw [haux]; exact hcountBlank _ (by simp [caller]))
  let C : Stacks tapes A := {F with R := Function.update F.R caller.count (List.replicate (N*(n*w)) tick)}
  have hca : caller.archive ≠ caller.count := selector_ne_aux _ _
  have hcs : caller.span ≠ caller.count := selector_ne_aux _ _
  have hcw : caller.controls 0 ≠ caller.count := selector_ne_aux _ _
  have hwhole := mn_seq_within_add (hwithin 0) hcount
  refine ⟨vf,C,m+l,huf.trans hu,Nat.add_le_add hm hl,Exec.seq he hcount.toExec,?_,?_⟩
  · constructor
    · simpa only [C,Function.update_of_ne hca] using hsrc
    · change (C.R caller.count).length = _
      simp only [C,Function.update_self,List.length_replicate,selectedRhsFields,List.length_map,
        Routing.RetainedFieldBatch.replicas_length]
      exact (Nat.mul_assoc N n w).symm
    · simpa only [C,Function.update_of_ne hcs] using hrows
    · simpa only [C,Function.update_of_ne hcw] using hwidth
    · have hne : selector (LocalRecoveryLayout.batch 2) ≠ caller.count := selector_ne_aux _ _
      change Function.update F.R caller.count _ (selector (LocalRecoveryLayout.batch 2)) = _
      rw [Function.update_of_ne hne]
      exact hqueueRestored
    · intro i
      have hne : selector (LocalRecoveryLayout.recovery i) ≠ caller.count := selector_ne_aux _ _
      change Function.update F.R caller.count _ (selector (LocalRecoveryLayout.recovery i)) = _
      rw [Function.update_of_ne hne]
      exact hrecovery i
    · exact left_count_update S F caller.count _ hleft
    · exact frame_count_update selector S F caller.count _ hframe
  · intro depth
    exact shiftStock hwhole depth


end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
