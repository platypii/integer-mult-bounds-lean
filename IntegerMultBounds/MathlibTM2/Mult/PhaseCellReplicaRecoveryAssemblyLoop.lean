module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryAssemblyRow
public import IntegerMultBounds.MathlibTM2.Host.ConsumeScan

/-! Final assembly is the existing paired consuming scan. It retains the
geometry master and needs only a single-row workspace reserve for all replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 12 Q A U}

def replicaRecoveryAssemblyLoop : Pr P 12 Q A U :=
  scanP 10 11 (retainedPackedPublicationMerge 0 1 2 3 4 5 6 7 8 9)

def ReplicaRecoveryAssemblyOutput {H : ReplicaHaloProblem s} {target : ℕ} {X : ℕ → ZMod s → ℝ}
    (B : ReplicaRecoveryBatch H target X) (Ds : List (ZMod s → GaussianInt))
    (r : Fin H.Fs.length) (words : List (Fin (A+4))) : Prop :=
  let E := B.recoveredField r (Ds.getD r.val (fun _ => 0))
  words = cstream A H.wordWidth (packedInterval H.origin H.span E) ∧
    (∀ i, Fits H.wordWidth (E i)) ∧
    PhaseCellInterface.ErrorOn (haloVertices s H.origin (H.origin+H.span))
      (fun i => (value H.precision (E i)).re) (X r.val) (1/(2 : ℝ)^target)

theorem replicaRecoveryAssemblyLoop_exec (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (B : ReplicaRecoveryBatch H target X) (htarget)
    (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (hDs : ∀ r : Fin H.Fs.length, ReplicaHaloRowSpec (B.problem htarget) r.val (Ds.getD r.val (fun _ => 0)))
    (hA : 4 ≤ A) (tailX tailY : List (Fin (A+4))) (v : HS 12 Q A U) (S : Stacks 12 A)
    (hmaster : S.R 0 = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin
      (H.origin+H.span) H.origin H.span)
    (hwidth : (S.R 2).length = H.wordWidth)
    (hX : S.R 4 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++tailX)
    (hY : S.R 5 = (List.ofFn B.boundary).flatMap
      (fun Y => cstream A H.wordWidth (packedInterval H.origin H.span Y))++tailY)
    (hfresh : ∀ k ∈ ([1,3,6,8,9,11] : List (Fin 12)), S.R k = [])
    (hcount : (S.R 10).length = H.Fs.length) (depth : ℕ) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ H.Fs.length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4 ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*retainedPackedPublicationMergeCost H.span H.wordWidth) depth
        replicaRecoveryAssemblyLoop (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 5 tailY)
          4 tailX) 7 (outputs.reverse.flatten++S.R 7))}) := by
  let enc := fun D : ZMod s → GaussianInt => cstream A H.wordWidth (packedInterval H.origin H.span D)
  let J := fun F : Stacks 12 A => ∀ k ∈ ([0,1,2,3,6,8,9] : List (Fin 12)), F.R k = S.R k
  have hflat (f : Fin H.Fs.length → ZMod s → GaussianInt) :
      (List.finRange H.Fs.length).flatMap (fun r => enc (f r)) = (List.ofFn f).flatMap enc := by
    simp only [List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def,List.map_map]
  have hfields : List.ofFn (fun r : Fin H.Fs.length => Ds.getD r.val (fun _ => 0)) = Ds := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      exact List.getD_eq_getElem _ _ hj
  suffices hscan : ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (List.finRange H.Fs.length).length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4 ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*retainedPackedPublicationMergeCost H.span H.wordWidth) depth
        replicaRecoveryAssemblyLoop (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 5 tailY)
          4 tailX) 7 (outputs.reverse.flatten++S.R 7))}) by
    simpa only [List.length_finRange] using hscan
  apply consumeScan_exec (body := body) (retainedPackedPublicationMerge 0 1 2 3 4 5 6 7 8 9)
    10 11 5 4 7 (by decide) (fun r => enc (B.boundary r))
    (fun r => enc (Ds.getD r.val (fun _ => 0))) (List.finRange H.Fs.length) tailY tailX
    (retainedPackedPublicationMergeCost H.span H.wordWidth)
    (2*retainedPackedPublicationMergeCost H.span H.wordWidth) depth (ReplicaRecoveryAssemblyOutput B Ds) J
    ?_ ?_ ?_ v S (fun _ _ => rfl) ?_ ?_ (by simpa using hcount) (hfresh 11 (by decide))
  · intro F R hR hJ k hk
    have hk10 : k ≠ 10 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk11 : k ≠ 11 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hR k hk10 hk11).trans (hJ k hk)
  · intro F otail rest words hJ k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hJ _ (by decide)
  · intro r hr vi F otail rest hJ hboundary hinterior
    obtain ⟨hfit,herror,v',n,hu,hn,he⟩ := B.assemble_row_exec (body := body) htarget r
      (Ds.getD r.val (fun _ => 0)) (hDs r) 0 1 2 3 4 5 6 7 8 9 (by decide) hA rest otail vi F
      ((hJ 0 (by decide)).trans hmaster) (by rw [hJ 2 (by decide)]; exact hwidth) hinterior hboundary
      ((hJ 1 (by decide)).trans (hfresh 1 (by decide)))
      ((hJ 3 (by decide)).trans (hfresh 3 (by decide)))
      ((hJ 6 (by decide)).trans (hfresh 6 (by decide)))
      ((hJ 8 (by decide)).trans (hfresh 8 (by decide)))
      ((hJ 9 (by decide)).trans (hfresh 9 (by decide))) depth
    refine ⟨v',n,enc (B.recoveredField r (Ds.getD r.val (fun _ => 0))),hu,hn,?_,⟨rfl,hfit,herror⟩,?_⟩
    · simp [enc,length_cstream,packedInterval_length _ H.span_fit]
    · apply he.cast rfl
      apply congrArg (mk v')
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk : k = 4 <;> simp [Function.update_apply,hk,enc]
  · rw [hflat]
    exact hY
  · rw [hflat,hfields]
    exact hX

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
