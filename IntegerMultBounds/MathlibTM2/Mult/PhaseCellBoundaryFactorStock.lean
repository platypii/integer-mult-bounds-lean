module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPermanentBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnfoldHeaderVolume

/-! A single per-register stock bound for the owned factor bank. The live RHS
port is excluded; all other high registers are retained across local solves. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast

def BoundaryFactorStock {A : ℕ} (S : Stacks 224 A) (D : ℕ) : Prop :=
  ∀ i : Fin 224, 154 ≤ i.val → i ≠ 206 → (S.R i).length ≤ D

def boundaryFactorStockBound (q w band N : ℕ) : ℕ :=
  boundaryPermanentSizeBound q band N+12*band*w+N*(12*band+1)

theorem boundaryFactorStock_of_bounds {A D H : ℕ} (S : Stacks 224 A)
    (hperm : BoundaryPermanentBound (boundaryFactorState S) D)
    (hheaders : boundaryUnfoldHeaderVolume (boundaryFactorState S) ≤ H)
    (hdout : boundaryFactorState S .dout = []) (h184 : S.R 184 = []) (h223 : S.R 223 = []) :
    BoundaryFactorStock S (D+H) := by
  intro i hi hi206
  by_cases hi184 : i = 184
  · subst i; simp [h184]
  by_cases hi223 : i = 223
  · subst i; simp [h223]
  obtain ⟨r,hr⟩ := boundaryFactorReg_cover i hi hi184 hi223
  have hrsrc : r ≠ .src := by
    intro he; subst r
    have hh := congrArg Fin.val hr
    change 140 = i.val at hh
    omega
  have hrvk : r ≠ .vk := by
    intro he; subst r
    exact hi206 hr.symm
  rw [← hr]
  change (boundaryFactorState S r).length ≤ D+H
  by_cases hrt : r ∈ boundaryTransientRoles
  · have hH : (boundaryFactorState S .m2wn).length+(boundaryFactorState S .kn).length+
        (boundaryFactorState S .tK).length+(boundaryFactorState S .sel).length ≤ H := hheaders
    simp only [boundaryTransientRoles,List.mem_cons,List.not_mem_nil,or_false] at hrt
    rcases hrt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hrsrc rfl)
    · omega
    · omega
    · omega
    · omega
    · exact False.elim (hrvk rfl)
    · simp [hdout]
  · exact (hperm r hrt).trans (Nat.le_add_right D H)

theorem BoundaryFactorStock.of_frame {A D : ℕ} {S F : Stacks 224 A}
    (h : BoundaryFactorStock S D)
    (hframe : ∀ i : Fin 224, 154 ≤ i.val → i ≠ 206 → F.R i = S.R i) :
    BoundaryFactorStock F D := by
  intro i hi hn
  rw [hframe i hi hn]
  exact h i hi hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
