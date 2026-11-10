module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBulkLocalRowSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedTensorLine
public import IntegerMultBounds.MathlibTM2.Routing.RetainedFieldBatch

/-! Generate one controller and scan the actual retained target batch into the
principal RHS ABI, preserving the prepared recovery bank and target archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.MathlibTM2.Routing.RetainedHaloTensor
noncomputable section
variable {ι : Type} [DecidableEq ι]
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

theorem retainedReplicaRhs_bounded (axis : ι → Axis) (retained : Finset ι)
    (f : (ι → ℕ) → GaussianInt) (before middle : List (Sum ι ι)) (a p : ℕ)
    (j : ι)
    (hf : ∀ x, (∀ k, x k < (axis k).N*(axis k).L) → ‖value p (f x)‖ ≤ 1) :
    ∀ F ∈ selectedRhsFields s
      ((Routing.RetainedFieldBatch.replicas axis retained before middle a).map
        (fun c => retainedTensorLine axis retained f c j)), ∀ k, ‖value p (F k)‖ ≤ 1 := by
  apply selectedRhsFields_bounded
  intro F hF k
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hF
  exact retainedTensorLine_bounded axis retained f c j p
    (Routing.RetainedFieldBatch.replicas_valid axis retained before middle a c hc) hf k

theorem preparedRetainedSelection_exec
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
    (hheaders : LocalSelectionHeaders A W V s ((axis i).N*(axis i).L) a (k*(axis i).L-(axis i).H) w n (embStk geometry S))
    (hclock : (S.R (batch 0)).length = ((middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod)) (hvolume : (S.R (batch 1)).length = ((axis i).L+2*(axis i).H)*w)
    (hqueue : S.R (batch 2) = Routing.RetainedFieldBatch.batch A w axis retained before middle i aPrefix k f++tail)
    (harchive : S.R (batch 3) = []) (hacc : S.R (batch 4) = [])
    (hdst : S.R source = []) (hline : S.R (geometry 110) = []) :
    ∃ (v' : HS tapes Q A U) (B : Stacks 117 A) (m : ℕ),
      let K := embOvr geometry B.get S
      let F := {K with R := (Function.update (Function.update K.R (batch 0) []) source
        (cstream A w ((selectedRhsFields s
          ((Routing.RetainedFieldBatch.replicas axis retained before middle aPrefix).map (fun c => retainedTensorLine axis retained f c i))).map (packedInterval a n)).flatten))}
      v'.user = v.user ∧ m ≤ preparedBulkSelectionCost W V ((axis i).L+2*(axis i).H) w n ((middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod) ∧
      Exec body preparedBulkSelection (Host.mk v S) m (Host.mk v' F) ∧
      (F.R source).length = (middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod*n*w ∧
      F.R rowCount = List.replicate n tick ∧ F.R (batch 2) = S.R (batch 2) ∧
      (∀ i, F.R (recovery i) = S.R (recovery i)) ∧
      (∀ i, F.R (scratch i) = S.R (scratch i)) ∧
      B.L = (embStk geometry S).L ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        3*preparedBulkSelectionCost W V ((axis i).L+2*(axis i).H) w n ((middle.map (Routing.RetainedTensorEnumeration.width axis retained)).prod)) depth preparedBulkSelection (Host.mk v S) m (Host.mk v' F) := by
  have hqueue' := hqueue
  dsimp only [Routing.RetainedFieldBatch.batch] at hqueue'
  simp only [localLength,ite_eq_left hi] at hqueue'
  rw [retainedTensorBatch_window A w axis retained f (Routing.RetainedFieldBatch.replicas axis retained before middle aPrefix) i hi k hH hguard] at hqueue'
  have hex := preparedBulkSelection_exec_base (body := body) hn hwide hwindow hwV hspan hvol hVW hA hVpos
    ((Routing.RetainedFieldBatch.replicas axis retained before middle aPrefix).map (fun c => retainedTensorLine axis retained f c i)) tail v S hheaders
    (by simpa only [List.length_map,Routing.RetainedFieldBatch.replicas_length] using hclock) hvolume hqueue' harchive hacc hdst hline
  have houtLen := selectedWindowPayload_length A w a n (k*(axis i).L-(axis i).H)
    ((axis i).L+2*(axis i).H)
    ((Routing.RetainedFieldBatch.replicas axis retained before middle aPrefix).map
      (fun c => retainedTensorLine axis retained f c i)) hsource hwindow
  rw [selectedWindowPayload_eq A w a n _ _ _ hsource hwindow] at houtLen
  simp only [List.length_map,Routing.RetainedFieldBatch.replicas_length] at houtLen
  simp only [selectedWindowPayload_eq A w a n _ _ _ hsource hwindow,List.length_map,
    Routing.RetainedFieldBatch.replicas_length] at hex
  obtain ⟨v',B,m,hu,hm,he,hrows,hqueueFinal,hrecovery,hscratch,hleft,hwithin⟩ := hex
  refine ⟨v',B,m,hu,hm,he,?_,hrows,hqueueFinal,hrecovery,hscratch,hleft,hwithin⟩
  simpa only [Function.update_self] using houtLen

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
