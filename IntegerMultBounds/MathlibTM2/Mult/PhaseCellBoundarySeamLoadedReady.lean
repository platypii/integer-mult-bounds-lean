module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamMasterLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamReady

/-! Interpret the actual copied headers as the persistent boundary controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T A s : ℕ}

def boundarySeamCropCount (slot : Fin 3) : Fin 117 := ⟨60+slot.val,by omega⟩
def boundarySeamSeedMaster : Fin 3 → Fin 11 := ![4,5,6]
def boundarySeamCropMaster (slot : Fin 3) : Fin 11 := ⟨8+slot.val,by omega⟩

structure BoundarySeamHeaderWords (p width W D N : ℕ) (seedValue : Fin 117 → ℕ)
    (words : Fin 11 → List (Fin (A+4))) : Prop where
  clock : (words 0).length = N
  line : (words 1).length = s
  wide : (words 2).length = W
  word : (words 3).length = 2*p+13
  seeds : ∀ j, words (boundarySeamSeedMaster j) = binSyms D (seedValue (boundarySeedGlobals j))
  ruler : (words 7).length = D
  crops : ∀ slot, (words (boundarySeamCropMaster slot)).length =
    coreLength s width (boundaryCropIndex s width slot)*(2*p+13)

noncomputable section
open PackedTranspose

theorem BoundarySeamReady.of_header_frame (p width W D N : ℕ) (seedValue : Fin 117 → ℕ)
    (words : Fin 11 → List (Fin (A+4))) (hwords : BoundarySeamHeaderWords (s := s) p width W D N seedValue words)
    (e : Fin 117 → Fin T) (hinj : Function.Injective e) (S F : Stacks T A)
    (hblank : ∀ i, i.val < 63 → i ≠ 95 → i ≠ 96 → S.R (e i) = [])
    (hloaded : ∀ i, F.R (e (boundarySeamMasterRole i)) = words i)
    (hframe : ∀ i, (∀ j, e (boundarySeamMasterRole j) ≠ i) → F.R i = S.R i) :
    BoundarySeamReady (s := s) p width W D N boundarySeamCropCount seedValue
      (embStk (e) F) := by
  have hget (i : Fin 11) : (embStk e F).R (boundarySeamMasterRole i) = words i := hloaded i
  have hz (i : Fin 117) (hi : i ∉ List.ofFn boundarySeamMasterRole) (hs : i ≠ 95) (hd : i ≠ 96) (hsmall : i.val < 63) :
      (embStk e F).R i = [] := by
    change F.R (e i) = []
    rw [hframe]
    · exact hblank i hsmall hs hd
    · intro j he
      exact hi (List.mem_ofFn.mpr ⟨j,hinj he⟩)
  have hzero (i : Fin 117) (hi : i ∈ [(59:Fin 117),26,24,54,19,27,28,29,20,21,22,23]) :
      (embStk e F).R i = [] := by
    have hstatic : ∀ i ∈ [(59:Fin 117),26,24,54,19,27,28,29,20,21,22,23],
        i ∉ List.ofFn boundarySeamMasterRole ∧ i ≠ 95 ∧ i ≠ 96 ∧ i.val < 63 := by decide +kernel
    exact hz i (hstatic i hi).1 (hstatic i hi).2.1 (hstatic i hi).2.2.1 (hstatic i hi).2.2.2
  refine ⟨?_,?_,hzero 59 (by simp),?_,?_,?_,?_,?_,hzero 27 (by simp),hzero 28 (by simp),
    hzero 29 (by simp),?_,?_,?_,?_,?_⟩
  · intro slot
    have := slot.isLt
    constructor <;> intro h <;> have hv := congrArg Fin.val h <;> simp [boundarySeamCropCount] at hv <;> omega
  · simpa only [show boundarySeamMasterRole 7 = 58 from by decide +kernel] using (congrArg List.length (hget 7)).trans hwords.ruler
  · intro j
    have h := hget (boundarySeamSeedMaster j)
    have hrole : boundarySeamMasterRole (boundarySeamSeedMaster j) = boundarySeedGlobals j := by
      fin_cases j <;> rfl
    rw [hrole] at h
    exact h.trans (hwords.seeds j)
  · intro r
    have hstatic : ∀ i : Fin 117, 30 ≤ i.val → i.val < 54 →
        i ∉ List.ofFn boundarySeamMasterRole ∧ i ≠ 95 ∧ i ≠ 96 := by decide +kernel
    have h := hstatic (boundaryCounterRegister r) (boundaryCounterRegister_bounds r).1
      (boundaryCounterRegister_bounds r).2
    exact hz _ h.1 h.2.1 h.2.2 (lt_trans (boundaryCounterRegister_bounds r).2 (by decide))
  · exact ⟨hzero 26 (by simp),hzero 24 (by simp),hzero 54 (by simp),hzero 19 (by simp)⟩
  · intro slot
    have hrole : boundarySeamMasterRole (boundarySeamCropMaster slot) = boundarySeamCropCount slot := by
      fin_cases slot <;> rfl
    rw [←hrole,hget]
    exact hwords.crops slot
  · intro i hi hne
    have hstatic : ∀ i ∈ standardSeamPublicationPlan.support,
        i ∉ List.ofFn boundarySeamMasterRole ∧ i ≠ 95 ∧ i ≠ 96 ∧ i.val < 63 := by decide +kernel
    exact hz i (hstatic i hi).1 (hstatic i hi).2.1 (hstatic i hi).2.2.1 (hstatic i hi).2.2.2
  · simpa only [show boundarySeamMasterRole 2 = 17 from by decide +kernel] using (congrArg List.length (hget 2)).trans hwords.wide
  · simpa only [show boundarySeamMasterRole 3 = 18 from by decide +kernel] using (congrArg List.length (hget 3)).trans hwords.word
  · simpa only [show boundarySeamMasterRole 0 = 15 from by decide +kernel] using (congrArg List.length (hget 0)).trans hwords.clock
  · simpa only [show boundarySeamMasterRole 1 = 16 from by decide +kernel] using (congrArg List.length (hget 1)).trans hwords.line
  · intro i hi
    exact hzero i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto)

theorem BoundarySeamReady.of_loaded_headers (p width W D N : ℕ) (seedValue : Fin 117 → ℕ)
    (words : Fin 11 → List (Fin (A+4))) (hwords : BoundarySeamHeaderWords (s := s) p width W D N seedValue words)
    (source destination : Fin T) (hne : source ≠ destination) (S F : Stacks (T+tapeCount) A)
    (hblank : ∀ i, i ≠ 95 → i ≠ 96 → S.R (seamRegister source destination i) = [])
    (hloaded : ∀ i, F.R (seamRegister source destination (boundarySeamMasterRole i)) = words i)
    (hframe : ∀ i, (∀ j, seamRegister source destination (boundarySeamMasterRole j) ≠ i) → F.R i = S.R i) :
    BoundarySeamReady (s := s) p width W D N boundarySeamCropCount seedValue
      (embStk (seamRegister source destination) F) := by
  exact BoundarySeamReady.of_header_frame p width W D N seedValue words hwords
    (seamRegister source destination) (seamRegister_injective source destination hne) S F (fun i _ hs hd => hblank i hs hd) hloaded hframe

theorem boundarySeamMasterLoad_ready_exec {Q : ℕ} {P U : Type}
    (body : P → Pr P (T+tapeCount) Q A U)
    (p width W D N : ℕ) (seedValue : Fin 117 → ℕ)
    (words : Fin 11 → List (Fin (A+4)))
    (hwords : BoundarySeamHeaderWords (s := s) p width W D N seedValue words)
    (source destination : Fin T) (hne : source ≠ destination) (masters : Fin 11 → Fin T)
    (v : HS (T+tapeCount) Q A U) (S : Stacks (T+tapeCount) A)
    (hsource : ∀ i, S.R (Fin.castAdd tapeCount (masters i)) = words i)
    (hblank : ∀ i, i ≠ 95 → i ≠ 96 → S.R (seamRegister source destination i) = [])
    (depth : ℕ) :
    let pairs := boundarySeamMasterCopies source destination masters
    let cost := (pairs.map (fun r => 6*(S.R r.1).length+6)).sum+1
    let F : Stacks (T+tapeCount) A := {S with R := copyWordHeadersR S.R pairs S.R}
    ∃ v', v'.user = v.user ∧
      BoundarySeamReady (s := s) p width W D N boundarySeamCropCount seedValue
        (embStk (seamRegister source destination) F) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*cost) depth
        (boundarySeamMasterLoad source destination masters) (mk v S) cost (mk v' F) := by
  dsimp only
  have hrole (i : Fin 11) : boundarySeamMasterRole i ≠ 95 ∧ boundarySeamMasterRole i ≠ 96 := by
    have h := boundarySeamMasterRole_off i
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact ⟨h.1,h.2.1⟩
  obtain ⟨v',hu,hget,hframe,he⟩ := boundarySeamMasterLoad_exec body source destination hne masters v S
    (hblank 27 (by decide) (by decide)) (hblank 28 (by decide) (by decide))
    (fun i => hblank _ (hrole i).1 (hrole i).2)
  refine ⟨v',hu,?_,?_⟩
  · exact BoundarySeamReady.of_loaded_headers p width W D N seedValue words hwords
      source destination hne S _ hblank (fun i => (hget i).trans (hsource i)) hframe
  · exact mn_native_exec_within he 2 (boundarySeamMasterLoad_native source destination masters)
      depth _ (by rfl)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
