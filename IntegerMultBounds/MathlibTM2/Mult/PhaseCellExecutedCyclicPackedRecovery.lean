module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPackedAssembly
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSecondInteriorAccuracy

/-! Ordinary inputs execute both recovery solves and both packed assembly loops.
The emitted piece streams represent the same certified full cyclic fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "extendAssembly" => CyclicPackedAssemblyPlacement.extend
local notation "extendSecond" => CyclicSecondInteriorPlacement.extend
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def executedCyclicPackedRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 850 Q A U :=
  .seq (embProg extendAssembly id (executedCyclicSecondInterior hR hQ)) cyclicPackedAssembly

theorem executedCyclicPackedRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let solveTarget := boundaryRecoveryTarget p target
    let cellTarget := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
    let q := executionPrecision p l cellTarget 2
    let w := executionWidth p l cellTarget 2
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
    ∀ (buffersL buffersR : ReplicaLoopBuffers A) (v : HS 850 Q A U) (S : Stacks 834 A)
      (tail pageTail : List (Fin (A+4))),
    CachedReplicaPassInput H CyclicReplicaPlacement.left buffersL S →
    CachedReplicaPassInput K CyclicReplicaPlacement.right buffersR S →
    CyclicResidualBatchInput p l s t u solveTarget a n tail pageTail (embStk CyclicReplicaPlacement.factorReg S) →
    S.R (CyclicReplicaPlacement.factorReg 226) = [] → S.R (CyclicReplicaPlacement.factorReg 229) = [] →
    ∃ (J L : ReplicaHaloProblem s) (X : Stacks 840 A) (vf : HS 850 Q A U) (G : Stacks 850 A)
      (fields : Fin Fs.length → ZMod s → GaussianInt) (steps : ℕ) (savedL savedR : List (Fin (A+4))),
      vf.user = v.user ∧
      CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      steps ≤ cachedCyclicReplicaBoundaryBill H K p u l t a n solveTarget q w B.card (24*band+1) Fs.length+
        solvedCyclicRecoveryCost H K Fs.length B.card n w+
        cyclicSecondInteriorTimeBudget H K p solveTarget B.card+
        ((Fs.length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4)+
          (Fs.length*(retainedPackedPublicationMergeCost K.span K.wordWidth+5)+4)) ∧
      G.R 848 = (List.ofFn (fun j => cstream A w (packedInterval a (min n (s-a)) (fields j)))).reverse.flatten ∧
      G.R 849 = (List.ofFn (fun j => cstream A w (packedInterval 0 (n-min n (s-a)) (fields j)))).reverse.flatten ∧
      G.R 247 = buffersL.accumulatorTail ∧ G.R 547 = buffersR.accumulatorTail ∧ G.R 125 = savedL ∧ G.R 425 = savedR ∧
      (∀ j : Fin Fs.length, (∀ i, Fits w (fields j i)) ∧ (∀ i, (fields j i).im = 0) ∧
        (∀ i ∉ cyclicPrincipalVertices s a n, fields j i = 0) ∧ ∀ x : ZMod s → ℝ,
          SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
            (fun i => (value q (Fs.getD j.val (fun _ => 0) i)).re) →
          PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
            (fun i => (value q (fields j i)).re) x (1/(2 : ℝ)^target)) ∧
      ReplicaAssemblyControls H (extendAssembly ∘ CyclicSecondInteriorPlacement.left.plan.gather)
        (extendAssembly (extendSecond (CyclicRecoveryPlacement.bank 239))) G ∧
      ReplicaAssemblyControls K (extendAssembly ∘ CyclicSecondInteriorPlacement.right.plan.gather)
        (extendAssembly (extendSecond (CyclicRecoveryPlacement.bank 238))) G ∧
      Exec (embTab extendAssembly (embTab extendSecond (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body))))
        (executedCyclicPackedRecovery hR hQ)
        (mk v (extendStacks (by decide : 842 ≤ 850) (extendStacks (by decide : 840 ≤ 842)
          (extendStacks (by decide : 834 ≤ 840) S)))) steps (mk vf G) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let solveTarget := boundaryRecoveryTarget p target
  let cellTarget := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
  let q := executionPrecision p l cellTarget 2
  let w := executionWidth p l cellTarget 2
  intro Fs hF
  let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
  let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
  have hHw : H.wordWidth = w := rfl
  have hKw : K.wordWidth = w := rfl
  have hHt : H.t = t := rfl
  have hKt : K.t = t := rfl
  have hHb : H.band = band := rfl
  have hKb : K.band = band := rfl
  have hHo : H.origin = a := rfl
  have hHs : H.span = min n (s-a) := rfl
  have hKo : K.origin = 0 := rfl
  have hKs : K.span = n-min n (s-a) := rfl
  intro buffersL buffersR v S tail pageTail inputsL inputsR factory h226 h229
  obtain ⟨solutions,J,L,X,z,F,m,savedL,savedR,hlen,hformat,haccuracy,layoutL,layoutR,hJtarget,hLtarget,
    hJexp,hLexp,hJFs,hLFs,hu,hm,hfieldsL,hfieldsR,harchiveL,harchiveR,hcontrolsL,hcontrolsR,he⟩ :=
    executedCyclicSecondInterior_spec (body := body) hR hQ hA axis ha hn hleftRoom hrightRoom
      Fs hF buffersL buffersR (embDn extendAssembly v) S tail pageTail inputsL inputsR factory h226 h229
  obtain ⟨Ds,Es,hDlen,hElen,hencD,hencE,hgood⟩ := cyclicSecondInterior_fields_target axis ha hn target Fs hF
    solutions J L hlen hformat haccuracy layoutL layoutR hJtarget hLtarget hJFs hLFs
    CyclicSecondInteriorPlacement.left.output CyclicSecondInteriorPlacement.right.output
    buffersL.accumulatorTail buffersR.accumulatorTail F hfieldsL hfieldsR
  let Y := fun j : Fin Fs.length => boundarySolutionField B (solutions.getD j.val [])
  let fields := fun j : Fin Fs.length => cyclicPublicationField t band a n
    (Ds.getD j.val (fun _ => 0)) (Es.getD j.val (fun _ => 0)) (Y j)
  let rowsL := (List.finRange Fs.length).map (fun j => (Ds.getD j.val (fun _ => 0),Y j))
  let rowsR := (List.finRange Fs.length).map (fun j => (Es.getD j.val (fun _ => 0),Y j))
  have enum {β : Type} (xs : List β) (default : β) (hxs : xs.length = Fs.length) :
      (List.finRange Fs.length).map (fun j => xs.getD j.val default) = xs := by
    simp only [List.finRange,List.map_ofFn,Function.comp_def]
    apply List.ext_getElem
    · simp only [List.length_ofFn,hxs]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      exact List.getD_eq_getElem _ _ hj
  have hmapD : rowsL.map Prod.fst = Ds := by
    simpa only [rowsL,List.map_map,Function.comp_def] using enum Ds (fun _ => 0) hDlen
  have hmapE : rowsR.map Prod.fst = Es := by
    simpa only [rowsR,List.map_map,Function.comp_def] using enum Es (fun _ => 0) hElen
  have hmapYL : rowsL.map Prod.snd = solutions.map (boundarySolutionField B) := by
    simpa only [rowsL,Y,List.map_map,Function.comp_def] using
      congrArg (List.map (boundarySolutionField B)) (enum solutions [] hlen)
  have hmapYR : rowsR.map Prod.snd = solutions.map (boundarySolutionField B) := by
    simpa only [rowsR,rowsL,List.map_map,Function.comp_def] using hmapYL
  have hylist : (cyclicBoundaryRecoveryRows B solutions Fs).reverse.map Prod.fst = solutions.map (boundarySolutionField B) := by
    simpa only [←List.map_reverse,List.reverse_reverse] using
      congrArg List.reverse (cyclicBoundaryRecoveryRows_fields B solutions Fs hlen)
  have hxLwords := congrArg (fun xs : List (ZMod s → GaussianInt) => xs.flatMap (cyclicRecoveryField (A := A) H)) hmapD
  have hxRwords := congrArg (fun xs : List (ZMod s → GaussianInt) => xs.flatMap (cyclicRecoveryField (A := A) K)) hmapE
  have hyLwords := congrArg (fun xs : List (ZMod s → GaussianInt) => xs.flatMap (cyclicRecoveryField (A := A) H))
    (hmapYL.trans hylist.symm)
  have hyRwords := congrArg (fun xs : List (ZMod s → GaussianInt) => xs.flatMap (cyclicRecoveryField (A := A) K))
    (hmapYR.trans hylist.symm)
  simp only [List.flatMap_map] at hxLwords hxRwords hyLwords hyRwords
  have hXL : F.R 247 = rowsL.flatMap (fun row => cyclicRecoveryField H row.1)++buffersL.accumulatorTail := by
    rw [hxLwords]
    change F.R 247 = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++buffersL.accumulatorTail
    rw [hHw]
    exact hencD
  have hXR : F.R 547 = rowsR.flatMap (fun row => cyclicRecoveryField K row.1)++buffersR.accumulatorTail := by
    rw [hxRwords]
    change F.R 547 = Es.flatMap (fun E => cstream A K.wordWidth (packedInterval K.origin K.span E))++buffersR.accumulatorTail
    rw [hKw]
    exact hencE
  have hYL : F.R 125 = rowsL.flatMap (fun row => cyclicRecoveryField H row.2)++savedL := by
    rw [hyLwords]; exact harchiveL
  have hYR : F.R 425 = rowsR.flatMap (fun row => cyclicRecoveryField K row.2)++savedR := by
    rw [hyRwords]; exact harchiveR
  obtain ⟨zi,hzi,huser,helift⟩ := exec_extendStacks (by decide : 842 ≤ 850) (ι := id)
    (body' := embTab extendAssembly (embTab extendSecond (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body))))
    (fun _ => rfl) he v rfl
  obtain ⟨vf,G,k,huf,hk,hwordsL,hwordsR,h247,h125,h547,h425,heAssembly,hinp,hout,hleft,hframe⟩ :=
    cyclicPackedAssembly_exec
      (body := embTab extendAssembly (embTab extendSecond (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body))))
      H K rowsL rowsR (by simp only [rowsL,List.length_map,List.length_finRange]; rfl)
      (by simp only [rowsR,List.length_map,List.length_finRange]; rfl) (by omega)
      buffersL.accumulatorTail savedL buffersR.accumulatorTail savedR zi F hcontrolsL hcontrolsR hXL hYL hXR hYR 0
  have hmem (b N i : ℕ) (hfit : b+N ≤ s) (hi : i < N) :
      ((b+i : ℕ) : ZMod s) ∈ haloVertices s b (b+N) := by
    apply (mem_haloVertices b (b+N) _).mpr
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : b+i < s)]
    omega
  have hwL : rowsL.map (fun row => cstream A H.wordWidth
      (packedInterval H.origin H.span (publicationField H.t H.band H.origin (H.origin+H.span) row.1 row.2))) =
      List.ofFn (fun j => cstream A w (packedInterval a (min n (s-a)) (fields j))) := by
    simp only [rowsL,List.finRange,List.map_ofFn,Function.comp_def,hHw,hHt,hHb,hHo,hHs]
    apply congrArg List.ofFn
    funext j
    apply congrArg (cstream A w)
    apply packedInterval_congr _ _ (by omega)
    intro i hi
    exact (cyclicPublicationField_left_of_real t band a n ha hn _ _ _ (hgood j).1
      (boundarySolutionField_im B (solutions.getD j.val [])) _ (hmem a _ i (by omega) hi)).symm
  have hwR : rowsR.map (fun row => cstream A K.wordWidth
      (packedInterval K.origin K.span (publicationField K.t K.band K.origin (K.origin+K.span) row.1 row.2))) =
      List.ofFn (fun j => cstream A w (packedInterval 0 (n-min n (s-a)) (fields j))) := by
    simp only [rowsR,List.finRange,List.map_ofFn,Function.comp_def,hKw,hKt,hKb,hKo,hKs,Nat.zero_add]
    apply congrArg List.ofFn
    funext j
    apply congrArg (cstream A w)
    apply packedInterval_congr _ _ (by omega)
    intro i hi
    exact (cyclicPublicationField_right_of_real t band a n ha hn _ _ _ (hgood j).2.1
      (boundarySolutionField_im B (solutions.getD j.val [])) _
      (by simpa only [Nat.zero_add] using hmem 0 _ i (by omega) hi)).symm
  rw [hwL] at hwordsL
  rw [hwR] at hwordsR
  have hk' : k ≤ (Fs.length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4)+
      (Fs.length*(retainedPackedPublicationMergeCost K.span K.wordWidth+5)+4) := by
    simpa only [rowsL,rowsR,List.length_map,List.length_finRange] using hk
  have hreadAssembly (i : Fin 842) :
      (extendStacks (by decide : 842 ≤ 850) F).R (extendAssembly i) = F.R i :=
    congrArg (fun C : Stacks 842 A => C.R i) (embStk_extendStacks (by decide : 842 ≤ 850) F)
  have hcontrolsLF : ReplicaAssemblyControls H
      (extendAssembly ∘ CyclicSecondInteriorPlacement.left.plan.gather)
      (extendAssembly (extendSecond (CyclicRecoveryPlacement.bank 239))) G := by
    apply hcontrolsL.transport
    · exact (hframe _ (by decide)).trans (hreadAssembly _)
    · intro i hi
      have hoff : extendAssembly (CyclicSecondInteriorPlacement.left.plan.gather i) ∉
          ([125,247,848,425,547,849] : List (Fin 850)) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
      exact (hframe _ hoff).trans (hreadAssembly _)
  have hcontrolsRF : ReplicaAssemblyControls K
      (extendAssembly ∘ CyclicSecondInteriorPlacement.right.plan.gather)
      (extendAssembly (extendSecond (CyclicRecoveryPlacement.bank 238))) G := by
    apply hcontrolsR.transport
    · exact (hframe _ (by decide)).trans (hreadAssembly _)
    · intro i hi
      have hoff : extendAssembly (CyclicSecondInteriorPlacement.right.plan.gather i) ∉
          ([125,247,848,425,547,849] : List (Fin 850)) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
      exact (hframe _ hoff).trans (hreadAssembly _)
  refine ⟨J,L,X,vf,G,fields,m+k,savedL,savedR,huf.trans (huser.trans hu),
    ⟨layoutL,layoutR,hJtarget,hLtarget,hJexp,hLexp⟩,Nat.add_le_add hm hk',
    hwordsL,hwordsR,h247,h547,h125,h425,?_,hcontrolsLF,hcontrolsRF,Exec.seq helift heAssembly.toExec⟩
  intro j
  exact ⟨(hgood j).2.2.1,cyclicPublicationField_im t band a n _ _ _ ,(hgood j).2.2.2.1,(hgood j).2.2.2.2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
