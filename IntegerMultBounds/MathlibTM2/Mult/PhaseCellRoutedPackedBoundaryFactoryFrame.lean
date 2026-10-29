module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedPackedBoundaryFactoryRelease

/-! A single retained-header frame carries factory output into the halo setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

theorem routedPackedBoundaryFactory_header_frame {A : ℕ} (S F : Stacks 242 A)
    (hlegacy : ∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg
        (embStk packedBoundaryTableRouting F))).R (boundaryFactorLegacyReg i) =
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg
        (embStk packedBoundaryTableRouting S))).R (boundaryFactorLegacyReg i))
    (hoff : ∀ k : Fin 242, (∀ i, packedBoundaryFactorReg i ≠ k) →
      (embStk packedBoundaryTableRouting F).L k = (embStk packedBoundaryTableRouting S).L k ∧
      (embStk packedBoundaryTableRouting F).R k = (embStk packedBoundaryTableRouting S).R k)
    (h132 : F.R 132 = S.R 132) :
    ∀ k : Fin 242, 117 ≤ k.val → k.val < 168 → k ≠ 143 → F.R k = S.R k := by
  intro k hk hk' h143
  by_cases h132k : k = 132
  · subst k; exact h132
  by_cases h140k : k = 140
  · subst k
    simpa [embStk,packedBoundaryTableRouting,Equiv.swap_apply_def] using (hoff 140 packedBoundaryFactorReg_ne_rows).2
  by_cases hlo : k.val < 154
  · let i : Fin 154 := ⟨k.val,hlo⟩
    have h109 : i ≠ 109 := by intro he; have hv := congrArg Fin.val he; dsimp [i] at hv; omega
    have h115 : i ≠ 115 := by intro he; have hv := congrArg Fin.val he; dsimp [i] at hv; omega
    have h116 : i ≠ 116 := by intro he; have hv := congrArg Fin.val he; dsimp [i] at hv; omega
    have h132i : i ≠ 132 := by
      intro he
      apply h132k
      apply Fin.ext
      exact congrArg (fun j : Fin 154 => j.val) he
    have hv132 : k.val ≠ 132 := fun he => h132k (Fin.ext he)
    have hv140 : k.val ≠ 140 := fun he => h140k (Fin.ext he)
    have hv143 : k.val ≠ 143 := fun he => h143 (Fin.ext he)
    have hindex : packedBoundaryTableRouting
        (packedBoundaryFactorReg (preparedBoundaryCoreReg (boundaryFactorLegacyReg i))) = k := by
      apply Fin.ext
      simp [packedBoundaryTableRouting,Equiv.swap_apply_def,packedBoundaryFactorReg,
        preparedBoundaryCoreReg,boundaryFactorLegacyReg,Fin.ext_iff,i,hv132,hv140,hv143,hlo,
        show k.val ≠ 206 by omega,show k.val ≠ 220 by omega]
    have hh := hlegacy i h109 h115 h116 h132i
    change F.R (packedBoundaryTableRouting (packedBoundaryFactorReg
      (preparedBoundaryCoreReg (boundaryFactorLegacyReg i)))) = S.R (packedBoundaryTableRouting
        (packedBoundaryFactorReg (preparedBoundaryCoreReg (boundaryFactorLegacyReg i)))) at hh
    rwa [hindex] at hh
  · have h220 : k ≠ 220 := by intro he; subst k; contradiction
    have hf := packedBoundaryTableRouting_fixed k h132k h220
    simpa only [embStk,Function.comp_apply,hf] using
      (hoff k (fun i => packedBoundaryFactorReg_avoids_metadata i k (by omega) hk')).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
