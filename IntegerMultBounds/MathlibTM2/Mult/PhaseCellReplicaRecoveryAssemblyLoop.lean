module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryAssemblyRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryAssemblyLoop

/-! Final assembly is the existing paired consuming scan. It retains the
geometry master and needs only a single-row workspace reserve for all replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 12 Q A U}

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
  have hflat (f : Fin H.Fs.length → ZMod s → GaussianInt) :
      (List.finRange H.Fs.length).flatMap (fun r => enc (f r)) = (List.ofFn f).flatMap enc := by
    simp only [List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def]
  have hfields : List.ofFn (fun r : Fin H.Fs.length => Ds.getD r.val (fun _ => 0)) = Ds := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      exact List.getD_eq_getElem _ _ hj
  let rows := (List.finRange H.Fs.length).map (fun r => (Ds.getD r.val (fun _ => 0),B.boundary r))
  have hXrows : S.R 4 = rows.flatMap (fun row => enc row.1)++tailX := by
    simpa only [rows,List.flatMap_map,hflat,hfields] using hX
  have hYrows : S.R 5 = rows.flatMap (fun row => enc row.2)++tailY := by
    simpa only [rows,List.flatMap_map,hflat] using hY
  obtain ⟨v',n,hu,hn,he⟩ := packedRecoveryAssemblyLoop_exec (body := body)
    H.t H.band H.origin H.span H.wordWidth H.s_lt_t H.span_fit rows hA tailX tailY v S
    hmaster hwidth hXrows hYrows hfresh (by simpa only [rows,List.length_map,List.length_finRange] using hcount) depth
  refine ⟨v',n,_,hu,?_,?_,he⟩
  · simpa only [rows,List.length_map,List.length_finRange] using hn
  · simp only [rows,List.map_map,List.forall₂_map_right_iff,List.forall₂_same]
    intro r hr
    obtain ⟨hfits,herror⟩ := B.accept_row htarget r _ (hDs r)
    exact ⟨rfl,hfits,herror⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
