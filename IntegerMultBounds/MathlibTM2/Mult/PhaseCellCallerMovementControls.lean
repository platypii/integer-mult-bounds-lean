module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGatherSeed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBankStock

/-! Allocate the retained movement counters from raw scalar counters. Word and
replica lengths use the shared copier; volume uses the existing unary product. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix
  ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T A s W N : ℕ}

def movementCopies (T : ℕ) (src : Fin 11 → Fin T) : List (Fin (MachineTapes T) × Fin (MachineTapes T)) :=
  [(unarySource T (src 7),fullHeader T .word),(unarySource T (src 8),fullHeader T .replicas)]

def movementControlProgram {Q : ℕ} {P U : Type} (src : Fin 11 → Fin T) : Pr P (MachineTapes T) Q A U :=
  .seq (copyUnaryHeaders (seedReg T (.z 0)) (movementCopies T src))
    (unaryProduct (unarySource T (src 4)) (fullHeader T .word) (fullHeader T .volume)
      (seedReg T (.z 0)) (seedReg T (.z 1)))

def movementControlCost (s W N : ℕ) : ℕ := (4*(W+N)+9)+(s*(4*W+9)+4)

theorem prepareMovementControls_exec_within {Q : ℕ} {P U : Type}
    (body : P → Pr P (MachineTapes T) Q A U) (src : Fin 11 → Fin T)
    (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hs : (S.R (unarySource T (src 4))).length = s)
    (hW : (S.R (unarySource T (src 7))).length = W)
    (hN : (S.R (unarySource T (src 8))).length = N)
    (hword : S.R (fullHeader T .word) = []) (hreplicas : S.R (fullHeader T .replicas) = [])
    (hvolume : S.R (fullHeader T .volume) = [])
    (hsaved : S.R (seedReg T (.z 0)) = []) (htmp : S.R (seedReg T (.z 1)) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧
      (F.R (fullHeader T .word)).length = W ∧
      (F.R (fullHeader T .replicas)).length = N ∧
      (F.R (fullHeader T .volume)).length = s*W ∧ F.L = S.L ∧
      (∀ k, k ≠ fullHeader T .word → k ≠ fullHeader T .replicas → k ≠ fullHeader T .volume → F.R k = S.R k) ∧
      n ≤ movementControlCost s W N ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*movementControlCost s W N) depth
        (movementControlProgram src) (Host.mk v S) n (Host.mk v' F) := by
  have hregs : ∀ q ∈ movementCopies T src, [q.1,q.2,seedReg T (.z 0)].Nodup := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · have hsrc : unarySource T (src 7) ≠ fullHeader T .word := (fullHeader_ne_bank id .word (src 7)).symm
      have ht := unarySource_ne_seed T (src 7) (.z 0)
      have hd := fullHeader_ne_seed T .word (.z 0)
      simp [List.nodup_cons,hsrc,ht,hd]
    · have hq' : q = (unarySource T (src 8),fullHeader T .replicas) := by simpa [movementCopies] using hq
      subst q
      have hsrc : unarySource T (src 8) ≠ fullHeader T .replicas := (fullHeader_ne_bank id .replicas (src 8)).symm
      have ht := unarySource_ne_seed T (src 8) (.z 0)
      have hd := fullHeader_ne_seed T .replicas (.z 0)
      simp [List.nodup_cons,hsrc,ht,hd]
  have hsep : ∀ q ∈ movementCopies T src, ∀ r ∈ movementCopies T src, q.2 ≠ r.1 := by
    intro q hq r hr
    simp only [movementCopies,List.mem_cons,List.not_mem_nil,or_false] at hq hr
    rcases hq with rfl | rfl <;> rcases hr with rfl | rfl
    all_goals exact fullHeader_ne_bank id _ _
  let M : Stacks (MachineTapes T) A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R (movementCopies T src)}
  have hoff (k) (hw : k ≠ fullHeader T .word) (hr : k ≠ fullHeader T .replicas) : M.R k = S.R k := by
    apply unaryCopiesR_off
    intro q hq
    simp only [movementCopies,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    · exact hw.symm
    · exact hr.symm
  have hwr : fullHeader T .word ≠ fullHeader T .replicas := (fullHeader_injective T).ne (by intro h; cases h)
  have hnd : ((movementCopies T src).map Prod.snd).Nodup := by simp [movementCopies,hwr]
  have hwordM : M.R (fullHeader T .word) = List.replicate W tick := by
    rw [show M.R (fullHeader T .word) = unaryCopiesR (fun k => (S.R k).length) S.R (movementCopies T src) (fullHeader T .word) from rfl]
    rw [unaryCopiesR_at _ _ _ hnd (unarySource T (src 7),fullHeader T .word) (by simp [movementCopies])]
    rw [hW,hword,List.append_nil]
  have hrepM : M.R (fullHeader T .replicas) = List.replicate N tick := by
    change unaryCopiesR (fun k => (S.R k).length) S.R (movementCopies T src) (fullHeader T .replicas) = _
    rw [unaryCopiesR_at _ _ _ hnd (unarySource T (src 8),fullHeader T .replicas) (by simp [movementCopies])]
    rw [hN,hreplicas,List.append_nil]
  have hcopyCost : copyUnaryHeadersCost (fun k => (S.R k).length) (movementCopies T src) = 4*(W+N)+9 := by
    simp [copyUnaryHeadersCost,movementCopies,hW,hN]
    omega
  obtain ⟨v₁,hu₁,he₁⟩ := copyUnaryHeaders_exec (body := body) (seedReg T (.z 0)) (movementCopies T src)
    hregs hsep (fun k => (S.R k).length) v S (fun _ _ => rfl) hsaved
  rw [hcopyCost] at he₁
  have hprod : [unarySource T (src 4),fullHeader T .word,fullHeader T .volume,seedReg T (.z 0),seedReg T (.z 1)].Nodup := by
    have hn : ([Sum.inl .word,Sum.inl .volume,Sum.inr (.z 0),Sum.inr (.z 1)] : List (Role ⊕ TblR 13)).Nodup := by simp
    have hb : [fullHeader T .word,fullHeader T .volume,seedReg T (.z 0),seedReg T (.z 1)].Nodup := hn.map (allocation_injective T)
    refine List.nodup_cons.mpr ⟨?_,hb⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨(fullHeader_ne_bank id .word (src 4)).symm,(fullHeader_ne_bank id .volume (src 4)).symm,
      unarySource_ne_seed T (src 4) (.z 0),unarySource_ne_seed T (src 4) (.z 1)⟩
  have hsM : (M.R (unarySource T (src 4))).length = s := by
    rw [hoff (unarySource T (src 4)) (fullHeader_ne_bank id .word (src 4)).symm (fullHeader_ne_bank id .replicas (src 4)).symm]
    exact hs
  have hvolumeM : M.R (fullHeader T .volume) = [] := by
    rw [hoff _ ((fullHeader_injective T).ne (by intro h; cases h)) ((fullHeader_injective T).ne (by intro h; cases h))]
    exact hvolume
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body) hprod v₁ M
    ((hoff _ (fullHeader_ne_seed T .word (.z 0)).symm (fullHeader_ne_seed T .replicas (.z 0)).symm).trans hsaved)
    ((hoff _ (fullHeader_ne_seed T .word (.z 1)).symm (fullHeader_ne_seed T .replicas (.z 1)).symm).trans htmp)
  rw [hsM,hwordM,List.length_replicate] at hn₂
  let F : Stacks (MachineTapes T) A := {M with R := Function.update M.R (fullHeader T .volume) (List.replicate (s*W) tick)}
  have he₂' : Exec body (unaryProduct (unarySource T (src 4)) (fullHeader T .word) (fullHeader T .volume)
      (seedReg T (.z 0)) (seedReg T (.z 1))) (Host.mk v₁ M) n₂ (Host.mk v₂ F) := by
    simpa only [hsM,hwordM,List.length_replicate,hvolumeM,List.append_nil] using he₂
  have hnative : mnNativePushBound 2 (movementControlProgram (Q := Q) (P := P) (A := A) (U := U) src) :=
    ⟨copyUnaryHeaders_native _ _,unaryProduct_native _ _ _ _ _⟩
  have he := Exec.seq he₁ he₂'
  refine ⟨v₂,F,_,hu₂.trans hu₁,?_,?_,?_,rfl,?_,Nat.add_le_add_left hn₂ _,?_⟩
  · simpa [F,(fullHeader_injective T).eq_iff] using congrArg List.length hwordM
  · simpa [F,(fullHeader_injective T).eq_iff] using congrArg List.length hrepM
  · simp [F]
  · intro k hw hr hv
    change Function.update M.R (fullHeader T .volume) (List.replicate (s*W) tick) k = S.R k
    rw [Function.update_of_ne hv]
    exact hoff k hw hr
  · exact mn_native_exec_within he 2 hnative depth _ (by unfold movementControlCost; omega)

/-- Turn the actual produced controls and their frame into the retained gather
contract. The original stream and private-storage hypotheses are preserved. -/
theorem movementRetainedInput {K : ℕ} {Fs : List (ZMod s → GaussianInt)}
    {borrowed : List (Fin (prime+K+4))} (b : ComputedClassBank → Fin T)
    (S F : Stacks (MachineTapes T) (prime+K))
    (hword : (F.R (fullHeader T .word)).length = W)
    (hreplicas : (F.R (fullHeader T .replicas)).length = Fs.length)
    (hvolume : (F.R (fullHeader T .volume)).length = s*W)
    (hL : F.L = S.L)
    (hframe : ∀ k, k ≠ fullHeader T .word → k ≠ fullHeader T .replicas → k ≠ fullHeader T .volume → F.R k = S.R k)
    (hsource : S.R (fullHeader T .input) = Fs.flatMap (fun C => cstream (prime+K) W (chirpLine s C))++borrowed)
    (hexposure : ∀ i : Fin 175, S.R (Fin.castAdd tapeCount (Fin.natAdd (T+headerCount) i)) = [])
    (houtput : S.R (fullExposedClassBank (bank b) (.control .source)) = [])
    (hroutingLeft : ∀ i : Fin tapeCount, S.L (Fin.natAdd ((T+headerCount)+175) i) = [])
    (hsourceLeft : S.L (control (fullExposedClassBank (bank b)) .source) = []) :
    GatherRetainedInput T K s W b Fs borrowed F := by
  refine {
    wordLength := hword
    volumeLength := hvolume
    replicaLength := hreplicas
    source := ?_
    exposureBlank := ?_
    outputBlank := ?_
    routingLeft := ?_
    sourceLeft := ?_}
  · rw [hframe]
    · exact hsource
    all_goals exact (fullHeader_injective T).ne (by intro h; cases h)
  · intro i
    rw [hframe]
    · exact hexposure i
    · exact exposurePrivate_ne_header T i .word
    · exact exposurePrivate_ne_header T i .replicas
    · exact exposurePrivate_ne_header T i .volume
  · rw [hframe]
    · exact houtput
    · exact (fullHeader_ne_numerical b .word (.control .source)).symm
    · exact (fullHeader_ne_numerical b .replicas (.control .source)).symm
    · exact (fullHeader_ne_numerical b .volume (.control .source)).symm
  · rw [hL]; exact hroutingLeft
  · rw [hL]; exact hsourceLeft

/-- The retained gather contract itself is an output of actual execution. -/
theorem prepareGatherControls_exec_within {Q K : ℕ} {P U : Type}
    {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
    (body : P → Pr P (MachineTapes T) Q (prime+K) U)
    (src : Fin 11 → Fin T) (b : ComputedClassBank → Fin T)
    (v : HS (MachineTapes T) Q (prime+K) U) (S : Stacks (MachineTapes T) (prime+K))
    (hs : (S.R (unarySource T (src 4))).length = s)
    (hW : (S.R (unarySource T (src 7))).length = W)
    (hN : (S.R (unarySource T (src 8))).length = Fs.length)
    (hword : S.R (fullHeader T .word) = []) (hreplicas : S.R (fullHeader T .replicas) = [])
    (hvolume : S.R (fullHeader T .volume) = [])
    (hsaved : S.R (seedReg T (.z 0)) = []) (htmp : S.R (seedReg T (.z 1)) = [])
    (hsource : S.R (fullHeader T .input) = Fs.flatMap (fun C => cstream (prime+K) W (chirpLine s C))++borrowed)
    (hexposure : ∀ i : Fin 175, S.R (Fin.castAdd tapeCount (Fin.natAdd (T+headerCount) i)) = [])
    (houtput : S.R (fullExposedClassBank (bank b) (.control .source)) = [])
    (hroutingLeft : ∀ i : Fin tapeCount, S.L (Fin.natAdd ((T+headerCount)+175) i) = [])
    (hsourceLeft : S.L (control (fullExposedClassBank (bank b)) .source) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ GatherRetainedInput T K s W b Fs borrowed F ∧
      F.L = S.L ∧
      (∀ k, k ≠ fullHeader T .word → k ≠ fullHeader T .replicas → k ≠ fullHeader T .volume → F.R k = S.R k) ∧
      n ≤ movementControlCost s W Fs.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*movementControlCost s W Fs.length) depth
        (movementControlProgram src) (Host.mk v S) n (Host.mk v' F) := by
  obtain ⟨v',F,n,hu,hw,hn,hv,hL,hframe,hcost,he⟩ :=
    prepareMovementControls_exec_within body src v S hs hW hN hword hreplicas hvolume hsaved htmp depth
  exact ⟨v',F,n,hu,movementRetainedInput b S F hw hn hv hL hframe hsource hexposure houtput hroutingLeft hsourceLeft,
    hL,hframe,hcost,he⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
