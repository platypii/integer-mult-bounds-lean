module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProcessReplicaHaloCell
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

def replicaHaloLoopCost (p l B s t u target rhsExp V a b : ℕ) (phases : List ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  (phases.map (fun phase => processReplicaCellCost p l B (haloLength s t band a b phase)
    s t u target rhsExp V (haloStart s t band a phase)+3)).sum+1

theorem replicaHaloLoop_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ℕ → ZMod s → ℝ)
    (hx : ∀ n < B, SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) (x n)
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (phases : List ℕ)
    (hphases : ∀ phase ∈ phases, phase ∈ haloCellPhases s t (PhaseCellBand.width p u) a b)
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed queueTail : List (Fin (A+4)))
    (hwide : s < 2^V)
    (hqueue : S.R 126 = replicaPhasePackets A V s t (PhaseCellBand.width p u) a b phases++queueTail)
    (hcount : S.R 127 = List.replicate phases.length tick)
    (hready : ReplicaCellReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) B V
      (executionWidth p l target rhsExp)
      (cstream A (executionWidth p l target rhsExp) (replicaAmbientWords B C)++borrowed) S)
    (hflag : v.flag = phases.head?.isSome) :
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ blocks : List (List (Fin (A+4))), v'.user = v.user ∧
      n ≤ replicaHaloLoopCost p l B s t u target rhsExp V a b phases ∧
      Exec (embTab groupReg body) (.loop (·.flag) (countedLoopBody 127 (processReplicaCell hR hQ)))
        (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = replicaLoopR S.R queueTail [] (blocks.reverse.flatten++S.R 93) ∧
      List.Forall₂ (fun phase ys => ReplicaBlockAccurate B (haloLength s t band a b phase)
        q w target (haloStart s t band a phase : ℕ) x ys) phases blocks := by
  dsimp only
  induction phases generalizing v S with
  | nil =>
    have hq : S.R 126 = queueTail := by simpa [replicaPhasePackets] using hqueue
    have hc : S.R 127 = [] := by simpa using hcount
    refine ⟨v,S,1,[],rfl,by simp [replicaHaloLoopCost],
      Exec.loop_false (by change v.flag = false; simpa using hflag),rfl,rfl,rfl,?_,.nil⟩
    have hh := replicaLoopR_self S.R
    rw [hq,hc] at hh
    simpa using hh.symm
  | cons phase phases ih =>
    let band := PhaseCellBand.width p u
    let rest := replicaPhasePackets A V s t band a b phases++queueTail
    let cs : List (Fin (A+4)) := List.replicate phases.length tick
    let S₀ : Stacks 144 A := {S with R := Function.update S.R 127 cs}
    have hframe₀ : S₀.R = replicaLoopR S.R (S.R 126) cs (S.R 93) := by
      funext k
      by_cases h126 : k = 126 <;> by_cases h127 : k = 127 <;> by_cases h93 : k = 93 <;>
        simp_all [S₀,replicaLoopR]
    have hready₀ := hready.of_frame (S' := S₀) (S.R 126) cs (S.R 93) rfl hframe₀
    have hphase := hphases phase (by simp)
    have hpos := ((mem_haloCellPhases s t band a b phase).mp hphase).2
    have hstart : haloStart s t band a phase < s := by
      have hh := haloStop_le s t band b phase
      dsimp only [haloLength] at hpos
      omega
    have hlo : ((haloStart s t band a phase : ℕ) : ZMod s).val = haloStart s t band a phase := by
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt hstart]
    have hpop : Exec (embTab groupReg body)
        (.act (.pop (.rt 127) (fun v _ => v) .done)) (mk v S) 1 (mk v S₀) := by
      simpa [S₀,cs,Action.run,update_rt,hcount,List.replicate_succ] using
        Exec.act (body := embTab groupReg body) (.pop (.rt 127) (fun v _ => v) .done) (mk v S)
    obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hi₁,ho₁,hl₁,hframe,hpoint,herror,ys,hylen,hys⟩ :=
      processReplicaHaloCell_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
        hB hphase hpad C hC x hx v S₀ borrowed hready₀.masters hready₀.left hready₀.blank
        hready₀.source hready₀.replicas hready₀.origin hready₀.keyWidth hwide rest
        (by simpa [S₀,rest,replicaPhasePackets,List.append_assoc,band,ZMod.val_natCast,Nat.mod_eq_of_lt hstart] using hqueue)
        hready₀.countSaved hready₀.headerTemp (hready₀.fresh 128 (by simp)) hready₀.wordWidth
        (by intro k hk; apply hready₀.fresh k
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)
    have hys' : S₁.R 93 = ys++S.R 93 := hys
    have hframe₁ : S₁.R = replicaLoopR S.R rest cs (ys++S.R 93) := by
      rw [hys'] at hframe
      exact hframe.trans (by
        funext k
        by_cases h126 : k = 126 <;> by_cases h127 : k = 127 <;> by_cases h93 : k = 93 <;>
          simp [S₀,replicaLoopR,Function.update_apply,h126,h127,h93])
    have hready₁ := hready.of_frame rest cs (ys++S.R 93) hl₁ hframe₁
    have hc₁ : S₁.R 127 = cs := by simpa [replicaLoopR] using congrArg (fun R => R 127) hframe₁
    have hq₁ : S₁.R 126 = rest := by simpa [replicaLoopR] using congrArg (fun R => R 126) hframe₁
    have hpeek := Exec.act (body := embTab groupReg body) (peekR 127) (mk v₁ S₁)
    rw [peekR_run,hc₁] at hpeek
    let v₁' : HS 144 Q A U := {v₁ with flag := cs.head?.isSome}
    obtain ⟨v₂,S₂,n₂,blocks,hu₂,hn₂,he₂,hi₂,ho₂,hl₂,hframe₂,hblocks⟩ :=
      ih (fun ph hph => hphases ph (by simp [hph])) v₁' S₁ hq₁ hc₁ hready₁
        (by dsimp [v₁',cs]; cases phases <;> rfl)
    have hblock : ReplicaBlockAccurate B (haloLength s t band a b phase)
        (executionPrecision p l target rhsExp) (executionWidth p l target rhsExp) target
        (haloStart s t band a phase : ℕ) x ys := by
      apply replicaBlockAccurate_of_append _ x ys (S.R 93) hylen
      simpa only [hys'] using hpoint
    refine ⟨v₂,S₂,1+(n₁+1)+n₂+1,ys::blocks,hu₂.trans hu₁,?_,
      Exec.loop_true (by change v.flag = true; simpa using hflag)
        (Exec.seq hpop (Exec.seq he₁ hpeek)) he₂,
      hi₂.trans hi₁,ho₂.trans ho₁,hl₂.trans hl₁,?_,.cons hblock hblocks⟩
    · dsimp only [replicaHaloLoopCost] at hn₂ ⊢
      simp only [List.map_cons,List.sum_cons]
      rw [hlo] at hn₁
      dsimp only [band] at hn₁
      omega
    · rw [hframe₂,hys',hframe₁,replicaLoopR_comp]
      simp only [List.reverse_cons,List.flatten_append,List.flatten_cons,List.flatten_nil,
        List.append_nil,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
