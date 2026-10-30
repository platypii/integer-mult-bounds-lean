module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedFreshOutputBank

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast ScalarPlacement

/-- Stable physical state between RHS replicas at one complete endpoint key. -/
structure PackedHaloBetweenInputs {A : ℕ}
    (P stage q l s t u band a b V w W boundaryCount : ℕ) (S : Stacks 248 A) : Prop where
  bank : PackedPreparedBank q w W boundaryCount (embStk packedBoundaryRecoveryBase S)
  headers : PackedHaloRetainedHeaders P stage q l s t u band a b V 0 (embStk packedRecoveryRuntimeReg S)
  native : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → S.R ⟨i.val,by omega⟩ = []
  scratch : ∀ k ∈ ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 248)), S.R k = []
  binaryLength : (S.R 157).length ≤ V
  privateBank : ∀ k : Fin 248, 242 ≤ k.val → S.L k = [] ∧ S.R k = []

/-- Retained header lengths are fixed throughout a batch at one numerical key. -/
theorem PackedHaloBetweenInputs.header_length_eq
    {A P stage q l s t u band a b V w W boundaryCount : ℕ} {S F : Stacks 248 A}
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S)
    (h' : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount F)
    (k : Fin 168) (hk : k ∈ haloRetainedHeaderPorts) :
    (F.R (packedRecoveryRuntimeReg k)).length = (S.R (packedRecoveryRuntimeReg k)).length :=
  h.headers.length_eq h'.headers k hk

/-- Restored native arithmetic registers contribute no prefix-dependent stock. -/
theorem PackedHaloBetweenInputs.native_length_eq
    {A P stage q l s t u band a b V w W boundaryCount : ℕ} {S F : Stacks 248 A}
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S)
    (h' : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount F)
    (k : Fin 117) (h93 : k ≠ 93) (h110 : k ≠ 110) :
    (F.R ⟨k.val,by omega⟩).length = (S.R ⟨k.val,by omega⟩).length := by
  rw [h.native k h93 h110,h'.native k h93 h110]

/-- Output allocation changes no between-input invariant. -/
theorem PackedHaloBetweenInputs.update_output
    {A P stage q l s t u band a b V w W boundaryCount : ℕ} {S : Stacks 248 A}
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S)
    (output : List (Fin (A+4))) :
    PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount
      {S with R := Function.update S.R 132 output} := by
  refine ⟨h.bank.update_output output,h.headers.update_output output,?_,?_,?_,?_⟩
  · intro i hi93 hi110
    have hi := i.isLt
    have h132 : (⟨i.val,by omega⟩ : Fin 248) ≠ 132 := by
      intro he; have hv := congrArg Fin.val he; change i.val = 132 at hv; omega
    simpa only [Function.update_of_ne h132] using h.native i hi93 hi110
  · intro k hk
    have h132 : k ≠ 132 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne h132] using h.scratch k hk
  · exact h.binaryLength
  · intro k hk
    have h132 : k ≠ 132 := by intro he; subst k; omega
    exact ⟨(h.privateBank k hk).1,by simpa only [Function.update_of_ne h132] using (h.privateBank k hk).2⟩

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 248 Q A U}

theorem PackedHaloBetweenInputs.allocate_exec
    {P stage q l s t u band a b V w W boundaryCount : ℕ}
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S)
    (hNV : b-a < 2^V) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedFreshOutputCost V (b-a) w ∧
      Exec body packedFreshOutput (IntegerMultBounds.MathlibTM2.Host.mk v S) n
        (IntegerMultBounds.MathlibTM2.Host.mk v' {S with R := Function.update S.R 132 (cstream A w (List.replicate (b-a) 0)++S.R 132)}) ∧
      PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount
        {S with R := Function.update S.R 132 (cstream A w (List.replicate (b-a) 0)++S.R 132)} := by
  obtain ⟨v',n,hu,hn,he,hbank,hpages⟩ := packedFreshOutput_prepared_exec V (b-a) w q W boundaryCount hNV v S
    h.headers.geometry.count (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.native 0 (by decide) (by decide)
      · exact h.native 1 (by decide) (by decide)
      · exact h.native 2 (by decide) (by decide)
      · exact (h.privateBank 246 (by decide)).2
      · exact (h.privateBank 247 (by decide)).2
      · exact (h.privateBank 242 (by decide)).2
      · exact (h.privateBank 243 (by decide)).2) h.bank
  exact ⟨v',n,hu,hn,he,h.update_output _⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
