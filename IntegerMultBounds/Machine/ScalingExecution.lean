import IntegerMultBounds.Machine.ScalingMerge
import IntegerMultBounds.Machine.ScalingPieceBridge
import IntegerMultBounds.Machine.ScalingSplitRewind

/-! End-to-end literal positive-unit scaling from a single raw payload tape.
The fixed machine splits the payload into contiguous buffers, physically
rewinds them, and merges blocks in inverse-scaled source order. Binary length
descriptors and one-hot control cells are explicit prepared inputs. -/

namespace IntegerMultBounds.Machine.ScalingExecution

open CountedCopyReuse (empty binary)

abbrev SplitTapes (c : ℕ) := 4+(c+c)
abbrev AuxTapes (c : ℕ) := 4+c+c+2
abbrev MergeTapes (c : ℕ) := 4+c+c+c+2
abbrev TapeCount (c : ℕ) := SplitTapes c + AuxTapes c

/-- Physical layout: split control, shared buffers, piece descriptors, then
merge control, modulus, current residue and outer-loop control. -/
def join {c : ℕ} (a : Tapes 4 0) (buffers descriptors : Tapes c 0)
    (b : Tapes 4 0) (modulus current : Tapes c 0) (outer : Tapes 2 0) : Tapes (TapeCount c) 0 :=
  (a.append (buffers.append descriptors)).append (((b.append modulus).append current).append outer)

private def activeTo {c : ℕ} : Fin (MergeTapes c) → Fin (TapeCount c) :=
  Fin.addCases
    (Fin.addCases
      (Fin.addCases
        (Fin.addCases
          (fun i => Fin.natAdd (SplitTapes c) (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c i))))
          (fun i => Fin.castAdd (AuxTapes c) (Fin.natAdd 4 (Fin.castAdd c i))))
        (fun i => Fin.natAdd (SplitTapes c) (Fin.castAdd 2 (Fin.castAdd c (Fin.natAdd 4 i)))))
      (fun i => Fin.natAdd (SplitTapes c) (Fin.castAdd 2 (Fin.natAdd (4+c) i))))
    (fun i => Fin.natAdd (SplitTapes c) (Fin.natAdd (4+c+c) i))

private def frameTo {c : ℕ} : Fin (4+c) → Fin (TapeCount c) :=
  Fin.addCases
    (fun i => Fin.castAdd (AuxTapes c) (Fin.castAdd (c+c) i))
    (fun i => Fin.castAdd (AuxTapes c) (Fin.natAdd 4 (Fin.natAdd c i)))

private def inverse {c : ℕ} : Fin (TapeCount c) → Fin (MergeTapes c+(4+c)) :=
  Fin.addCases
    (Fin.addCases
      (fun i => Fin.natAdd (MergeTapes c) (Fin.castAdd c i))
      (Fin.addCases
        (fun i => Fin.castAdd (4+c) (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c (Fin.natAdd 4 i)))))
        (fun i => Fin.natAdd (MergeTapes c) (Fin.natAdd 4 i))))
    (Fin.addCases
      (Fin.addCases
        (Fin.addCases
          (fun i => Fin.castAdd (4+c) (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c (Fin.castAdd c i)))))
          (fun i => Fin.castAdd (4+c) (Fin.castAdd 2 (Fin.castAdd c (Fin.natAdd (4+c) i)))))
        (fun i => Fin.castAdd (4+c) (Fin.castAdd 2 (Fin.natAdd (4+c+c) i))))
      (fun i => Fin.castAdd (4+c) (Fin.natAdd (4+c+c+c) i)))

/-- Static wiring identifies the same shared buffer tapes in split and merge.
This only defines placement of finite transition tables; it performs no move. -/
def placement (c : ℕ) : Fin (MergeTapes c+(4+c)) ≃ Fin (TapeCount c) where
  toFun := Fin.addCases activeTo frameTo
  invFun := inverse
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          induction i using Fin.addCases with
          | left i =>
            induction i using Fin.addCases <;>
              simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
          | right i => simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
        | right i => simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
    | right i =>
      induction i using Fin.addCases <;>
        simp only [frameTo,inverse,Fin.addCases_left,Fin.addCases_right]
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => simp only [frameTo,inverse,Fin.addCases_left,Fin.addCases_right]
      | right i =>
        induction i using Fin.addCases <;>
          simp only [activeTo,frameTo,inverse,Fin.addCases_left,Fin.addCases_right]
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          induction i using Fin.addCases <;>
            simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
        | right i => simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [activeTo,inverse,Fin.addCases_left,Fin.addCases_right]

/-- Projection of the physically shared data bank into the merge's local view. -/
theorem active_join {c : ℕ} (a : Tapes 4 0) (buffers descriptors : Tapes c 0)
    (b : Tapes 4 0) (modulus current : Tapes c 0) (outer : Tapes 2 0) :
    Placement.active (placement c) (join a buffers descriptors b modulus current outer) =
      ((((b.append buffers).append modulus).append current).append outer) := by
  unfold Placement.active placement join
  congr 1 <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases <;> simp [activeTo,Tapes.append]
      | right i => simp [activeTo,Tapes.append]
    | right i => simp [activeTo,Tapes.append]
  | right i => simp [activeTo,Tapes.append]

theorem extra_join {c : ℕ} (a : Tapes 4 0) (buffers descriptors : Tapes c 0)
    (b : Tapes 4 0) (modulus current : Tapes c 0) (outer : Tapes 2 0) :
    Placement.extra (placement c) (join a buffers descriptors b modulus current outer) = a.append descriptors := by
  unfold Placement.extra placement join
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp only [Equiv.coe_fn_mk,frameTo,Tapes.append,Fin.addCases_left,Fin.addCases_right]

/-- Replacing the active merge bank preserves the complete original input and
piece descriptor tapes in the complementary frame. -/
theorem replace_join {c : ℕ} (a : Tapes 4 0) (buffers buffers' descriptors : Tapes c 0)
    (b b' : Tapes 4 0) (modulus modulus' current current' : Tapes c 0) (outer outer' : Tapes 2 0) :
    Placement.replace (placement c) (join a buffers descriptors b modulus current outer)
      ((((b'.append buffers').append modulus').append current').append outer') =
      join a buffers' descriptors b' modulus' current' outer' := by
  rw [Placement.replace,extra_join,← extra_join a buffers' descriptors b' modulus' current' outer',
    ← active_join a buffers' descriptors b' modulus' current' outer']
  exact Placement.view _ _

private def splitControl (source : ℤ → Fin 4) (p : ℤ) : Tapes 4 0 :=
  CountedCopyReuse.bank source (fun _ => blank) empty (fun _ => blank) p 0 1 0

private def mergeControl (dest : ℤ → Fin 4) (q : ℤ) (bs : List Bool) : Tapes 4 0 :=
  CountedCopyReuse.bank empty dest empty (binary bs) 0 q 1 1

private def descriptorBank {c : ℕ} (descriptors : Fin c → List Bool) : Tapes c 0 :=
  ⟨fun _ => 1,fun j => binary (descriptors j)⟩

/-- Explicit prepared controls, all untouched by splitting and buffer rewinds. -/
def auxiliary {c : ℕ} (hc : 0 < c) (Q : ℕ) (dest : ℤ → Fin 4) (q : ℤ)
    (bs countBits : List Bool) (modulus current : Tapes c 0) : Tapes (AuxTapes c) 0 :=
  (((mergeControl dest q bs).append (OneHot.bank modulus (ScalingControl.residue hc Q))).append
    (OneHot.bank current (ScalingControl.residue hc 0))).append
    (CountedLoopReuse.controls empty (binary countBits) 1 1)

/-- Source payload block order, before applying the multiplication permutation. -/
def inputWord (Q : ℕ) (payload : ℕ → List (Fin 4)) : List (Fin 4) :=
  ((List.range Q).map payload).flatten

/-- Actual initial bank: one full source word and untouched separate buffers.
Both fixed residue banks and all immutable binary descriptors are supplied. -/
def input {c : ℕ} (hc : 0 < c) (Q : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    Tapes (TapeCount c) 0 :=
  (ScalingSplit.bank (putWord source p (inputWord Q payload)) background descriptors p origins).append
    (auxiliary hc Q dest q bs countBits modulus current)

/-- Entire global bank during the merge. The split's source head remains after
the whole input; split descriptors and original source contents are framed. -/
def state {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0)
    (payload : ℕ → List (Fin 4)) (z : ℕ) : Tapes (TapeCount c) 0 :=
  join (splitControl (putWord source p (inputWord Q payload)) (p+Q*B))
    (ScalingMerge.sources hc Q B background origins payload z) (descriptorBank descriptors)
    (mergeControl (putWord dest q (ScalingMerge.outputPrefix hc Q z payload)) (q+((z*B : ℕ) : ℤ)) bs)
    (OneHot.bank modulus (ScalingControl.residue hc Q))
    (OneHot.bank current (ScalingControl.residue hc z))
    (CountedLoopReuse.controls empty (binary countBits) 1 1)

theorem active_state {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0)
    (payload : ℕ → List (Fin 4)) (z : ℕ) :
    Placement.active (placement c)
      (state hc Q B source p background origins dest q descriptors bs countBits modulus current payload z) =
    CountedLoopReuse.bank (ScalingMerge.state hc Q B background origins dest q bs modulus current payload z)
      empty (binary countBits) 1 1 := by
  rw [state,active_join]
  rfl

private theorem prepared_state {Q c B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (p : ℤ) (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4))
    (hwidth : ∀ y, (payload y).length = B) :
    (ScalingSplit.bank (putWord source p (inputWord Q payload))
      (fun j => putWord (background j) (origins j) (ScalingSplit.piece Q c B (inputWord Q payload) j))
      descriptors (p+Q*B) origins).append (auxiliary hc Q dest q bs countBits modulus current) =
    state hc Q B source p background origins dest q descriptors bs countBits modulus current payload 0 := by
  have hsource : (⟨origins,fun j => putWord (background j) (origins j)
      (ScalingSplit.piece Q c B (inputWord Q payload) j)⟩ : Tapes c 0) =
      ScalingMerge.sources hc Q B background origins payload 0 := by
    unfold ScalingMerge.sources
    congr 1
    · funext j
      simp [ScalingMergeData.popCount]
    · funext j
      rw [inputWord,ScalingPieceBridge.piece_eq_blocks hc j payload (fun y _ => hwidth y)]
  unfold ScalingSplit.bank auxiliary state join splitControl mergeControl descriptorBank
  rw [hsource]
  simp [ScalingMerge.outputPrefix,putWord]

/-- Fixed-c program: every source piece is copied and physically rewound before
the statically placed merge starts. The join is a charged actual transition. -/
def program {c : ℕ} (hc : 0 < c) :
    Program (TapeCount c) ((ScalingSplit.states c+ScalingSplit.states c)+(7+(c*16+1+2+5)+4)) 0 :=
  seq (extend (ScalingSplitRewind.splitAndRewindProgram c) (AuxTapes c))
    (Placement.placed (ScalingMerge.program hc) (placement c))

/-- Complete correctness and transition bound from the original source tape.
The output contains the inverse-scaled whole blocks; source cells, backgrounds,
and all descriptors are preserved, and all mutable binary clocks are restored. -/
theorem scaling_hoare {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (hB : 0 < B) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (hb : Counter.value bs = B) (hn : Counter.value countBits = Q)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits)
    (payload : ℕ → List (Fin 4))
    (hp : ∀ j, Counter.value (descriptors j) = (ScalingSplit.piece Q c B (inputWord Q payload) j).length)
    (cp : ∀ j, GrowingCounterData.Canonical (descriptors j))
    (modulus current : Tapes c 0) (hwidth : ∀ y, (payload y).length = B) :
    HoareTime (program hc)
      (fun v => v = input hc Q source p background origins dest q descriptors bs countBits modulus current payload)
      (fun v => v = state hc Q B source p background origins dest q descriptors bs countBits modulus current payload Q)
      (75*(Q*B)+48*c+25) := by
  have hlen : (inputWord Q payload).length = Q*B := by
    unfold inputWord
    rw [BlockRotationData.uniform_volume B]
    · simp
    · intro block hm
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hm
      exact hwidth y
  have hs := (ScalingSplitRewind.splitAndRewind_hoare_linear hc source background descriptors p origins
    (inputWord Q payload) hlen hp cp).extend (auxiliary hc Q dest q bs countBits modulus current)
  have hsplit : HoareTime (extend (ScalingSplitRewind.splitAndRewindProgram c) (AuxTapes c))
      (fun v => v = input hc Q source p background origins dest q descriptors bs countBits modulus current payload)
      (fun v => v = state hc Q B source p background origins dest q descriptors bs countBits modulus current payload 0)
      (24*(Q*B)+48*c+1) := by
    apply hs.consequence _ _ le_rfl
    · rintro v rfl
      exact ⟨_,rfl,rfl⟩
    · rintro v ⟨w,rfl,rfl⟩
      exact prepared_state hc source p background origins dest q descriptors bs countBits modulus current payload hwidth
  have hm := Placement.hoare_at
    (ScalingMerge.merge_hoare_linear hQ hc hcop hB background origins dest q bs countBits hb hn cb cn
      modulus current payload hwidth) (placement c)
    (state hc Q B source p background origins dest q descriptors bs countBits modulus current payload 0)
    (active_state hc Q B source p background origins dest q descriptors bs countBits modulus current payload 0)
  have hmerge : HoareTime (Placement.placed (ScalingMerge.program hc) (placement c))
      (fun v => v = state hc Q B source p background origins dest q descriptors bs countBits modulus current payload 0)
      (fun v => v = state hc Q B source p background origins dest q descriptors bs countBits modulus current payload Q)
      (51*(Q*B)+23) := by
    apply hm.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    change Placement.replace (placement c) (state hc Q B source p background origins dest q descriptors
      bs countBits modulus current payload 0)
      (CountedLoopReuse.bank (ScalingMerge.state hc Q B background origins dest q bs modulus current payload Q)
        empty (binary countBits) 1 1) = _
    unfold state CountedLoopReuse.bank ScalingMerge.state ScalingMerge.bank ScalingMerge.core
    exact replace_join _ _ _ _ _ _ _ _ _ _ _ _
  apply (hsplit.seq hmerge).consequence (fun _ h => h) (fun _ h => h) _
  omega

/-- The global output tape slot is fixed solely by the coefficient. -/
def destinationSlot (c : ℕ) : Fin (TapeCount c) :=
  Fin.natAdd (SplitTapes c) (Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c (1 : Fin 4))))

/-- The concrete final destination tape contains the promised permuted payload. -/
theorem output_tape {c : ℕ} (hc : 0 < c) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (background : Fin c → ℤ → Fin 4) (origins : Fin c → ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (descriptors : Fin c → List Bool)
    (bs countBits : List Bool) (modulus current : Tapes c 0) (payload : ℕ → List (Fin 4)) :
    (state hc Q B source p background origins dest q descriptors bs countBits modulus current payload Q).tape
      (destinationSlot c) = putWord dest q (ScalingMerge.outputPrefix hc Q Q payload) := by
  simp [state,join,destinationSlot,Tapes.append,mergeControl,CountedCopyReuse.bank]

/-- In forward coordinates, the block written at c*y modulo Q is the exact
original source block y. Internal symbol order is never changed. -/
theorem block_at_destination {Q c y : ℕ} (hQ : 0 < Q) (hc : 0 < c)
    (hcop : c.Coprime Q) (hy : y < Q) (payload : ℕ → List (Fin 4)) :
    ((List.range Q).map
      (fun z => payload (ScalingPieces.restore Q c z (ScalingControl.select hc Q z).val)))[ScalingPieces.output Q c y]? = some (payload y) := by
  rw [List.getElem?_map,List.getElem?_range (ScalingPieces.output_lt hQ),Option.map_some,
    ScalingMergeData.restored_output hQ hc hcop hy]

/-- Neither tape count nor state count depends on Q, B or payload data. -/
theorem tapeCount_eq (c : ℕ) : TapeCount c = 10+4*c := by
  dsimp [TapeCount,SplitTapes,AuxTapes]
  omega

theorem stateCount_eq (c : ℕ) :
    (ScalingSplit.states c+ScalingSplit.states c)+(7+(c*16+1+2+5)+4) = 48*c+21 := by
  rw [ScalingSplit.states_eq]
  omega

end IntegerMultBounds.Machine.ScalingExecution
