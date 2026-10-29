module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace

/-! A flat placement reserves the packed geometry and coefficient-row port while
letting the existing factor kernel consume the actual folded RHS on 143. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def packedBoundaryFactorReg (i : Fin 226) : Fin 242 :=
  if i = 140 then 240 else if i = 143 then 241 else if i = 206 then 143 else
    ⟨if i.val < 154 then i.val else i.val+14,by split_ifs <;> have hi := i.isLt <;> omega⟩

private def packedBoundaryFactorBack (j : Fin 242) : Fin 226 :=
  ⟨if j.val = 240 then 140 else if j.val = 241 then 143 else if j.val = 143 then 206 else
    if j.val < 154 then j.val else j.val-14,by split_ifs <;> have hj := j.isLt <;> omega⟩

private theorem packedBoundaryFactorBack_place (i : Fin 226) :
    packedBoundaryFactorBack (packedBoundaryFactorReg i) = i := by
  by_cases h140 : i = 140
  · subst i; decide
  by_cases h143 : i = 143
  · subst i; decide
  by_cases h206 : i = 206
  · subst i; decide
  have hv143 : i.val ≠ 143 := fun he => h143 (Fin.ext he)
  have hi := i.isLt
  apply Fin.ext
  by_cases hlo : i.val < 154
  · simp [packedBoundaryFactorReg,packedBoundaryFactorBack,h140,h143,h206,hlo,hv143,
      show i.val ≠ 240 by omega,show i.val ≠ 241 by omega]
  · simp [packedBoundaryFactorReg,packedBoundaryFactorBack,h140,h143,h206,hlo,
      show i.val+14 ≠ 240 by omega,show i.val+14 ≠ 241 by omega,
      show i.val+14 ≠ 143 by omega,show ¬ i.val+14 < 154 by omega]

theorem packedBoundaryFactorReg_injective : Function.Injective packedBoundaryFactorReg := by
  intro i j he
  exact (packedBoundaryFactorBack_place i).symm.trans
    ((congrArg packedBoundaryFactorBack he).trans (packedBoundaryFactorBack_place j))

/-- The binary geometry bank is outside the factor workspace. -/
theorem packedBoundaryFactorReg_avoids_metadata (i : Fin 226) (k : Fin 242)
    (hk : 154 ≤ k.val) (hk' : k.val < 168) : packedBoundaryFactorReg i ≠ k := by
  intro he
  have hv := congrArg (fun j : Fin 242 => j.val) he
  unfold packedBoundaryFactorReg at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

/-- The coefficient page's row-width header is retained separately. -/
theorem packedBoundaryFactorReg_ne_rows (i : Fin 226) : packedBoundaryFactorReg i ≠ 140 := by
  intro he
  have hv := congrArg (fun j : Fin 242 => j.val) he
  unfold packedBoundaryFactorReg at hv
  split_ifs at hv <;> (try simp only at hv)
  all_goals omega

/-- Every owned high factor register stays above the halo runtime. -/
theorem packedBoundaryFactorReg_high_range (i : Fin 226) (hi : 154 ≤ i.val) (hn : i ≠ 206) :
    168 ≤ (packedBoundaryFactorReg i).val ∧ (packedBoundaryFactorReg i).val < 240 := by
  have hi226 := i.isLt
  have h140 : i ≠ 140 := by intro he; subst i; omega
  have h143 : i ≠ 143 := by intro he; subst i; omega
  simp [packedBoundaryFactorReg,h140,h143,hn,show ¬ i.val < 154 by omega]
  omega

def packedBoundaryNormalizeReg (i : Fin 224) : Fin 242 := packedBoundaryFactorReg ⟨i.val,by omega⟩

theorem packedBoundaryNormalizeReg_injective : Function.Injective packedBoundaryNormalizeReg := by
  intro i j he
  have hh := packedBoundaryFactorReg_injective he
  exact Fin.ext (congrArg (fun k : Fin 226 => k.val) hh)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
