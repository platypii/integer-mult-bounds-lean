module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryUnscale
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolveReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCyclicResidualPhysical

/-! The solved bank exposes exactly the physical controls needed for exact unscaling. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor

structure BoundaryUnscaleReady {A : ℕ} (q : ℕ) (S : Stacks 224 A) : Prop where
  left : ∀ i, S.L i = []
  mul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []
  ready : RsbReady (boundaryFactorState S) (2*q+8) q
  master : (S.R 119).length = q
  clean : ∀ k ∈ [(184 : Fin 224),220,221,223,208,215,211,201,206], S.R k = []

theorem boundaryUnscaleReady_of_solved {A q W N : ℕ} (S F : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hready : BoundarySolveReady (boundaryFactorState S) q (2*q+8) W N)
    (hmaster : (S.R 119).length = q)
    (hclean : ∀ k ∈ [(184 : Fin 224),220,221,223], S.R k = [])
    (hframe : RsbFr boundaryFactorReg S F) (output : List (Fin (A+4)))
    (hstate : boundaryFactorState F = Function.update (Function.update (boundaryFactorState S) .vk []) .dout output) :
    BoundaryUnscaleReady q F := by
  constructor
  · intro i
    rw [hframe.2.2.1]
    exact hleft i
  · intro i
    exact (hframe.2.2.2 _ (fun r => boundaryFactorReg_disjoint r i)).trans (hmul i)
  · rw [hstate]
    exact (hready.ready.update .vk (fun _ => by simp) []).update .dout (fun _ => by simp) output
  · rw [hframe.2.2.2 119 (fun r => boundaryFactorReg_off r 119 (by decide))]
    exact hmaster
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hframe.2.2.2 184 (fun r => (boundaryFactorReg_private r).1)).trans (hclean 184 (by simp))
    · have hh := congrFun hstate .dtab
      exact hh.trans (hclean 220 (by simp))
    · have hh := congrFun hstate .padc
      exact hh.trans (hclean 221 (by simp))
    · exact (hframe.2.2.2 223 (fun r => (boundaryFactorReg_private r).2)).trans (hclean 223 (by simp))
    · have hh := congrFun hstate .ya
      exact hh.trans (hready.empty .ya (by simp [boundarySolveScratch]))
    · have hh := congrFun hstate .ac2
      exact hh.trans (hready.empty .ac2 (by simp [boundarySolveScratch]))
    · have hh := congrFun hstate .xs
      exact hh.trans (hready.empty .xs (by simp [boundarySolveScratch]))
    · have hh := congrFun hstate .tC
      exact hh.trans (hready.empty .tC (by simp [boundarySolveScratch]))
    · have hh := congrFun hstate .vk
      change F.R 206 = _ at hh
      simpa using hh

theorem BoundaryUnscaleReady.update_accumulator {A q : ℕ} {S : Stacks 224 A}
    (h : BoundaryUnscaleReady q S) (tail : List (Fin (A+4))) :
    BoundaryUnscaleReady q {S with R := Function.update S.R 132 tail} := by
  constructor
  · exact h.left
  · intro i
    have hne : boundaryFactorMulReg i ≠ 132 := by
      intro he
      have hv := congrArg (fun k : Fin 224 => k.val) he
      change i.val = 132 at hv
      have := i.isLt
      omega
    simpa only [Function.update_of_ne hne] using h.mul i
  · rw [boundaryFactorState_update_accumulator]
    exact h.ready
  · simpa using h.master
  · intro k hk
    have hne : k ≠ 132 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hne] using h.clean k hk

theorem BoundaryUnscaleReady.update_solution {A q : ℕ} {S : Stacks 224 A}
    (h : BoundaryUnscaleReady q S) (output : List (Fin (A+4))) :
    BoundaryUnscaleReady q {S with R := Function.update S.R 217 output} := by
  constructor
  · exact h.left
  · intro i
    have hne : boundaryFactorMulReg i ≠ 217 := by
      intro he
      have hv := congrArg (fun k : Fin 224 => k.val) he
      change i.val = 217 at hv
      have := i.isLt
      omega
    simpa only [Function.update_of_ne hne] using h.mul i
  · rw [show boundaryFactorState {S with R := Function.update S.R 217 output} =
        Function.update (boundaryFactorState S) .dout output from boundaryFactorState_update S .dout output]
    exact h.ready.update .dout (fun _ => by simp) output
  · simpa using h.master
  · intro k hk
    have hne : k ≠ 217 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hne] using h.clean k hk

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem generatedBoundaryUnscale_ready_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q p : ℕ) (hpq : p ≤ q/2) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1)
    (v : HS 224 Q A U) (S : Stacks 224 A) (hready : BoundaryUnscaleReady q S)
    (hsrc : S.R 217 = cstream A (2*q+8) xs) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedBoundaryUnscaleCost q xs.length ∧
      Exec body (generatedBoundaryUnscale hQ) (mk v S) m
        (mk v' {S with R := Function.update S.R 217 (cstream A (2*q+8) (xs.map (unscaleBoundaryWord q)))}) := by
  exact generatedBoundaryUnscale_exec hQ hA q p hpq xs hbound v S hready.left hready.mul hready.ready hready.master
    (hready.clean 184 (by simp)) (hready.clean 220 (by simp)) (hready.clean 221 (by simp))
    (hready.clean 223 (by simp)) (hready.clean 208 (by simp)) (hready.clean 215 (by simp)) hsrc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
