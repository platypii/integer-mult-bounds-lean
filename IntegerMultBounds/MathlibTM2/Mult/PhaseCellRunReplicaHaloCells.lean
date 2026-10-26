module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloLoop
public import IntegerMultBounds.NLogN.PhaseCellHaloVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloRead
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaLoopFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBlock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.NLogN.PhaseCellHaloLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeReplicaCell
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGroupRHS
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassFrame

/-! Execute a shared same-origin replica solve, retire its gathered RHS, and
restore the raw source and outer registers while retaining the solved output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def runReplicaHaloCells (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  countedLoop 127 (processReplicaCell hR hQ)

theorem runReplicaHaloCells_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ℕ → ZMod s → ℝ)
    (hx : ∀ n < B, SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) (x n)
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed queueTail : List (Fin (A+4)))
    (hwide : s < 2^V)
    (hqueue : S.R 126 = haloDescriptorPackets A V s t (PhaseCellBand.width p u) a b++queueTail)
    (hcount : S.R 127 = List.replicate (haloCellPhases s t (PhaseCellBand.width p u) a b).length tick)
    (hready : ReplicaCellReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) B V
      (executionWidth p l target rhsExp)
      (cstream A (executionWidth p l target rhsExp) (replicaAmbientWords B C)++borrowed) S) :
    let phases := haloCellPhases s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ blocks : List (List (Fin (A+4))), v'.user = v.user ∧
      n ≤ replicaHaloLoopCost p l B s t u target rhsExp V a b phases+1 ∧
      Exec (embTab groupReg body) (runReplicaHaloCells hR hQ)
        (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = replicaLoopR S.R queueTail [] (blocks.reverse.flatten++S.R 93) ∧
      blocks.reverse.flatten.length = B*(haloInterior s t band a b).card*w ∧
      List.Forall₂ (fun phase ys => ReplicaBlockAccurate B (haloLength s t band a b phase)
        q w target (haloStart s t band a phase : ℕ) x ys) phases blocks ∧
      ∀ n : Fin B, PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (replicaBlocksRead q w n t band a b phases blocks) (x n) (1/(2 : ℝ)^target) := by
  dsimp only
  let phases := haloCellPhases s t (PhaseCellBand.width p u) a b
  have hpeek := Exec.act (body := embTab groupReg body) (peekR 127) (mk v S)
  rw [peekR_run,hcount] at hpeek
  let v₀ : HS 144 Q A U := {v with flag := (List.replicate phases.length (tick : Fin (A+4))).head?.isSome}
  obtain ⟨v',S',n,blocks,hu',hn,he,hi,ho,hl,hframe,hblocks⟩ :=
    replicaHaloLoop_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hB hpad
      C hC x hx phases (fun _ hp => hp) v₀ S borrowed queueTail hwide
      (by simpa only [replicaPhasePackets,haloDescriptorPackets] using hqueue) hcount hready
      (by dsimp [v₀]; cases phases <;> rfl)
  refine ⟨v',S',1+n,blocks,hu',(by dsimp only [phases] at hn; omega),Exec.seq hpeek he,hi,ho,hl,hframe,?_,hblocks,?_⟩
  · have hv := replicaBlocks_volume x (haloLength s t (PhaseCellBand.width p u) a b)
      (fun phase => (haloStart s t (PhaseCellBand.width p u) a phase : ℕ)) hblocks
    rw [haloCellPhases_volume hst] at hv
    exact hv
  · intro n
    exact replicaBlocksRead_errorOn hst (PhaseCellBand.width p u) a b x blocks hblocks n

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
