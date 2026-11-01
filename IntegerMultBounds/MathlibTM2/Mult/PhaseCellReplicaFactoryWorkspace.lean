module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBetweenInputs

/-! The physical facts needed from factor generation after width installation
and geometry retirement. The prepared bank supplies arithmetic left workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def replicaFactoryScratchPorts : List (Fin 242) :=
  [125,127,129,131,133,134,135,136,138,139,140,143,153,158,166,167]

structure ReplicaFactoryWorkspace {A : ℕ} (S : Stacks 242 A) : Prop where
  native : ∀ i : Fin 117, S.R (Fin.castLE (by decide) i) = []
  scratch : ∀ k ∈ replicaFactoryScratchPorts, S.R k = []
  maskLeft : S.L 167 = []

theorem ReplicaFactoryWorkspace.of_between {A P stage q l s t u band a b V w W N : ℕ}
    {S : Stacks 242 A}
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W N (extendStacks (by decide) S))
    (h93 : S.R 93 = []) (h110 : S.R 110 = []) (hmask : S.L 167 = []) : ReplicaFactoryWorkspace S := by
  refine ⟨?_,?_,hmask⟩
  · intro i
    by_cases hi93 : i = 93
    · subst i; exact h93
    by_cases hi110 : i = 110
    · subst i; exact h110
    have hh := h.native i hi93 hi110
    have hi := i.isLt
    simp only [extendStacks,show i.val < 242 by omega,↓reduceDIte] at hh
    exact hh
  · intro k hk
    have hh := h.scratch (Fin.castLE (by decide) k) (by
      simp only [replicaFactoryScratchPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
      norm_num at hk ⊢
      omega)
    simp only [extendStacks,Fin.val_castLE,k.isLt,↓reduceDIte] at hh
    exact hh

theorem ReplicaFactoryWorkspace.of_frame {A : ℕ} {S F : Stacks 242 A}
    (h : ReplicaFactoryWorkspace S)
    (hnative : ∀ i : Fin 117, F.R (Fin.castLE (by decide) i) = S.R (Fin.castLE (by decide) i))
    (hshared : ∀ k ∈ replicaFactoryScratchPorts, F.R k = S.R k)
    (hmask : F.L 167 = S.L 167) : ReplicaFactoryWorkspace F := by
  refine ⟨?_,?_,hmask.trans h.maskLeft⟩
  · intro i; exact (hnative i).trans (h.native i)
  · intro k hk; exact (hshared k hk).trans (h.scratch k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
