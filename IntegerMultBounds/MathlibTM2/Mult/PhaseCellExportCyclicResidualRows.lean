module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicReplicaBoundaryBatch

/-! Place actual residual packets on the existing shared solver's RHS port.
The replica count is borrowed from its retained master; packed controls retire. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def cyclicResidualRowsReg (i : Fin 180) : Fin 234 :=
  if i = 6 then 226 else if i = 179 then 229 else ⟨i.val,by omega⟩

theorem cyclicResidualRowsReg_injective : Function.Injective cyclicResidualRowsReg := by
  intro i j he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  have hj := j.isLt
  unfold cyclicResidualRowsReg at hv
  split_ifs at hv <;> simp_all only
  all_goals omega

def cyclicResidualRowsRetired : List (Fin 234) := [130,168,169,170,171,172,173]

def exportedCyclicResidualRows {A : ℕ} (S : Stacks 234 A) (rows : List (Fin (A+4))) : Stacks 234 A :=
  {S with R := fun k => if k ∈ cyclicResidualRowsRetired then [] else Function.update S.R 226 rows k}

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 234 Q A U}

def exportCyclicResidualRows : Pr P 234 Q A U :=
  .seq (embProg cyclicResidualRowsReg Empty.elim (initializedCyclicReplicaBoundaryBatch (P := Empty)))
    (clearWords [130,168,170,171,173])

def exportCyclicResidualRowsCost (replicas n N w : ℕ) :=
  initializedCyclicReplicaBoundaryBatchCost replicas n N w+(2*(w+n*w+n)+11)

theorem exportCyclicResidualRows_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (pairs : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt))) (w : ℕ)
    (v : HS 234 Q A U) (S : Stacks 234 A)
    (inputs : CyclicReplicaBoundaryInputs (s := s) t band a n w (embStk cyclicResidualRowsReg S))
    (hblank : ∀ r : Fin 180, r.val < 6 → S.R (cyclicResidualRowsReg r) = [])
    (hleft : S.R 169 = pairs.flatMap (fun z => cstream A w (packedInterval a (min n (s-a)) z.1)))
    (hright : S.R 172 = pairs.flatMap (fun z => cstream A w (packedInterval 0 (n-min n (s-a)) z.2)))
    (hreplicas : (S.R 229).length = pairs.length)
    (h176 : S.R 176 = []) (h177 : S.R 177 = []) (h178 : S.R 178 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ exportCyclicResidualRowsCost pairs.length n (cyclicPrincipalBoundary s t band a n).card w ∧
      Exec body exportCyclicResidualRows (mk v S) m
        (mk v' (exportedCyclicResidualRows S
          (pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))))) := by
  let rowStream := pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))
  obtain ⟨vi,m₁,hui,hm₁,hei⟩ := initializedCyclicReplicaBoundaryBatch_exec
    (body := fun z : Empty => nomatch z) hst hA band a n ha hn pairs w [] []
    (embDn cyclicResidualRowsReg v) (embStk cyclicResidualRowsReg S) inputs hblank
    (by simpa [embStk,cyclicResidualRowsReg] using hleft)
    (by simpa [embStk,cyclicResidualRowsReg] using hright)
    (by simpa [embStk,cyclicResidualRowsReg] using hreplicas)
    (by simpa [embStk,cyclicResidualRowsReg] using h176)
    (by simpa [embStk,cyclicResidualRowsReg] using h177)
    (by simpa [embStk,cyclicResidualRowsReg] using h178)
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    cyclicResidualRowsReg_injective (fun z => nomatch z) hei v rfl S rfl
  let J : Stacks 234 A := {S with R := (Function.update (Function.update (Function.update S.R 169 []) 172 []) 226 rowStream)}
  have he₁' : Exec body (embProg cyclicResidualRowsReg Empty.elim (initializedCyclicReplicaBoundaryBatch (P := Empty)))
      (mk v S) m₁ (mk v₁ J) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    rw [embOvr_updateR_updateR_updateR cyclicResidualRowsReg_injective]
    rfl
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) [130,168,170,171,173] (by decide) v₁ J
  have hwidth : (S.R 130).length = w := by
    simpa [embStk,cyclicResidualRowsReg] using inputs.width
  have hleftVolume : (S.R 168).length = min n (s-a)*w := by
    simpa [embStk,cyclicResidualRowsReg] using inputs.leftVolume
  have hrightVolume : (S.R 171).length = (n-min n (s-a))*w := by
    simpa [embStk,cyclicResidualRowsReg] using inputs.rightVolume
  have hleftMask : (S.R 170).length = min n (s-a) := by
    simpa [embStk,cyclicResidualRowsReg] using congrArg List.length inputs.leftMask
  have hrightMask : (S.R 173).length = n-min n (s-a) := by
    simpa [embStk,cyclicResidualRowsReg] using congrArg List.length inputs.rightMask
  have hclear : 2*([(130 : Fin 234),168,170,171,173].map (fun r => (J.R r).length)).sum+
      2*([(130 : Fin 234),168,170,171,173].length)+1 = 2*(w+n*w+n)+11 := by
    simp [J,hwidth,hleftVolume,hrightVolume,hleftMask,hrightMask]
    have hsplit := Nat.sub_add_cancel (Nat.min_le_left n (s-a))
    nlinarith only [hsplit,congrArg (fun k => k*w) hsplit]
  have hfinal : {J with R := fun k => if k ∈ [(130 : Fin 234),168,170,171,173] then [] else J.R k} =
      exportedCyclicResidualRows S rowStream := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ [(130 : Fin 234),168,170,171,173]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals simp [exportedCyclicResidualRows,cyclicResidualRowsRetired]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
      by_cases h169 : k = 169 <;> by_cases h172 : k = 172
      all_goals simp [J,exportedCyclicResidualRows,cyclicResidualRowsRetired,hk.1,hk.2.1,hk.2.2.1,
        hk.2.2.2.1,hk.2.2.2.2,h169,h172,Function.update_apply]
  refine ⟨v₂,_,hu₂.trans (hu₁.trans hui),?_,(Exec.seq he₁' he₂).cast rfl (congrArg (mk v₂) hfinal)⟩
  simpa only [hclear,exportCyclicResidualRowsCost] using Nat.add_le_add_right hm₁ (2*(w+n*w+n)+11)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
