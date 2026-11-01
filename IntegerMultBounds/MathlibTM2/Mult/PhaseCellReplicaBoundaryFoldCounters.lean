module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFoldCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFoldPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Generate the retained fold counters once at their scratch-compatible ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

def replicaBoundaryFoldCounters : Pr P 242 Q A U :=
  embProg replicaBoundaryFoldBank Empty.elim (packedBoundaryFoldCounters (P := Empty))

def replicaBoundaryFoldCounterState (n w : ℕ) (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := (Function.update (Function.update (Function.update S.R
    117 (List.replicate (n/2) tick)) 118 (List.replicate ((n+1)/2-n/2) tick))
    120 (List.replicate (((n+1)/2)*w) tick))}

theorem replicaBoundaryFoldCounters_exec (n w : ℕ) (v : HS 242 Q A U) (S : Stacks 242 A)
    (hn : (S.R 116).length = n) (hw : (S.R 130).length = w)
    (hblank : ∀ k ∈ [(1 : Fin 242),4,5,117,118,120], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ boundaryFoldCountersCost n w ∧
      Exec body replicaBoundaryFoldCounters (mk v S) m (mk v' (replicaBoundaryFoldCounterState n w S)) := by
  obtain ⟨vi,m,hu,hm,he⟩ := packedBoundaryFoldCounters_exec (body := fun z : Empty => nomatch z)
    n w (embDn replicaBoundaryFoldBank v) (embStk replicaBoundaryFoldBank S)
    (by change (S.R (replicaBoundaryFoldBank 116)).length = n
        rw [replicaBoundaryFoldBank_fixed _ (by decide)]; exact hn)
    (by change (S.R (replicaBoundaryFoldBank 130)).length = w
        rw [replicaBoundaryFoldBank_fixed _ (by decide)]; exact hw) (by
      intro i hi
      change S.R (replicaBoundaryFoldBank i) = []
      have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by omega
      rcases hv with hv | hv | hv | hv | hv | hv
      all_goals first
        | (have heq : i = 0 := Fin.ext hv; subst i; simpa using hblank 117 (by simp))
        | (have heq : i = 1 := Fin.ext hv; subst i; rw [replicaBoundaryFoldBank_fixed _ (by decide)]; exact hblank 1 (by simp))
        | (have heq : i = 2 := Fin.ext hv; subst i; simpa using hblank 118 (by simp))
        | (have heq : i = 3 := Fin.ext hv; subst i; simpa using hblank 120 (by simp))
        | (have heq : i = 4 := Fin.ext hv; subst i; rw [replicaBoundaryFoldBank_fixed _ (by decide)]; exact hblank 4 (by simp))
        | (have heq : i = 5 := Fin.ext hv; subst i; rw [replicaBoundaryFoldBank_fixed _ (by decide)]; exact hblank 5 (by simp)))
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    replicaBoundaryFoldBank_injective (fun z => nomatch z) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  let J := embStk replicaBoundaryFoldBank S
  let K : Stacks 168 A := {J with R := Function.update J.R 0 (List.replicate (n/2) tick)}
  let L : Stacks 168 A := {K with R := Function.update K.R 2 (List.replicate ((n+1)/2-n/2) tick)}
  let F : Stacks 168 A := {L with R := Function.update L.R 3 (List.replicate (((n+1)/2)*w) tick)}
  change embOvr replicaBoundaryFoldBank F.get S = _
  dsimp only [F]
  rw [embOvr_updR replicaBoundaryFoldBank_injective]
  dsimp only [L]
  rw [embOvr_updR replicaBoundaryFoldBank_injective]
  dsimp only [K,J]
  rw [embOvr_updR replicaBoundaryFoldBank_injective,embOvr_stk]
  simp only [replicaBoundaryFoldBank_floor,replicaBoundaryFoldBank_parity,replicaBoundaryFoldBank_bytes]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
