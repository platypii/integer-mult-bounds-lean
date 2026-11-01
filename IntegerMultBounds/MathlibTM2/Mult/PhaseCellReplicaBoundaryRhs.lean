module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFoldPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem

/-! Concrete reusable headers for the archive-to-RHS controller. Fold counters
live outside multiplier scratch; mask and volumes are shared by every row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

structure ReplicaBoundaryRhsReady (H : ReplicaHaloProblem s) (S : Stacks 242 A) : Prop where
  volume : (S.R 123).length = H.span*H.wordWidth
  rhsVolume : (S.R 124).length = (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth
  mask : S.R 167 = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span
  width : (S.R 130).length = H.wordWidth
  count : (S.R 116).length = (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card
  floor : (S.R 117).length = (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card/2
  parity : (S.R 118).length = ((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)/2-
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card/2
  bytes : (S.R 120).length = ((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)/2*H.wordWidth
  saved : S.R 104 = []
  tmp : S.R 105 = []
  rhs : S.R 143 = []
  scratch : ∀ k : Fin 242, k.val < 77 → S.R k = []

def replicaBoundaryRhs : Pr P 242 Q A U :=
  prepareReplicaBoundaryRhs replicaBoundaryFoldBank 123 238 124 143 0 1 2 3 4 104 105

def replicaBoundaryRhsCost (H : ReplicaHaloProblem s) :=
  let N := (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card
  stageReplicaBoundaryRhsCost H.span H.wordWidth+60*(N+1)*H.wordWidth+60*N+60+6*(N*H.wordWidth)+6

theorem replicaBoundaryRhs_exec (H : ReplicaHaloProblem s) (hA : 4 ≤ A)
    (D : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 242 Q A U) (S : Stacks 242 A)
    (h : ReplicaBoundaryRhsReady H S)
    (harchive : S.R 238 = cstream A H.wordWidth (packedInterval H.origin H.span D)++tail) :
    ∃ v' m, v'.user = v.user ∧ m ≤ replicaBoundaryRhsCost H ∧
      Exec body replicaBoundaryRhs (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 238 tail) 143
          (cstream A H.wordWidth ((bFoldOrder s (haloBoundary s H.t H.band H.origin (H.origin+H.span))).map
            (fun i => realPartWord (D i)))))}) := by
  have hB : ∀ i ∈ haloBoundary s H.t H.band H.origin (H.origin+H.span),
      H.origin ≤ i.val ∧ i.val < H.origin+H.span := by
    intro i hi
    exact (mem_haloVertices _ _ _).mp (Finset.mem_sdiff.mp hi).1
  obtain ⟨v',m,hu,hm,he⟩ := prepareReplicaBoundaryRhs_exec (body := body)
    replicaBoundaryFoldBank replicaBoundaryFoldBank_injective 123 238 124 143 0 1 2 3 4 104 105
    (by decide) (by decide) (by decide) replicaBoundaryFoldBank_ne_archive (by decide)
    H.s_lt_t hA H.band H.origin (H.origin+H.span) H.span_fit H.span_fit hB D H.wordWidth tail v S
    h.rhsVolume h.volume harchive (by rw [replicaBoundaryFoldBank_fixed _ (by decide)]; exact h.mask)
    (by rw [replicaBoundaryFoldBank_fixed _ (by decide)]; exact h.width) h.saved h.tmp
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> exact h.scratch _ (by decide))
    (by rw [replicaBoundaryFoldBank_fixed _ (by decide)]; exact h.rhs)
    (by rw [replicaBoundaryFoldBank_fixed _ (by decide)]; exact h.count)
    (by simpa using h.floor) (by simpa using h.parity) (by simpa using h.bytes)
    (by intro i hi6 hi77; rw [replicaBoundaryFoldBank_scratch i hi6 hi77]; exact h.scratch _ hi77)
  exact ⟨v',m,hu,hm,by simpa only [replicaBoundaryRhs,h.rhs,List.append_nil] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
