module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareClassInputs

/-! Reclaim the two generated masters and their narrow geometry export after
publication. Only the ambient output differs from the pre-setup state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem retireGeneratedClass_exec_within (body : P → Pr P T Q A U)
    (core halo header output : Fin T) (hne : [core,halo,header].Nodup)
    (hout : ∀ k ∈ [core,halo,header], output ≠ k)
    (B D : ℕ) (clipped : Bool) (s width radius : ℕ)
    (ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ k ∈ [core,halo,header], S.R k = []) (depth : ℕ) :
    let M := classInputsLoaded core halo header B D clipped s width radius S
    let F := {M with R := Function.update M.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords [core,halo,header]) (mk v F) (4*D+2*B+7)
        (mk v' {S with R := Function.update S.R output ys}) := by
  dsimp only
  have hr := hne
  regs_ne hr
  let M := masterLoaded core halo D clipped s width radius S
  let H : Stacks T A := {M with R := Function.update M.R header (binSyms B (haloRows clipped s width radius))}
  let F : Stacks T A := {H with R := Function.update H.R output ys}
  have hoc : output ≠ core := hout core (by simp)
  have hoh : output ≠ halo := hout halo (by simp)
  have hohead : output ≠ header := hout header (by simp)
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [core,halo,header] hne v F
  have hcost : 2*(([core,halo,header].map (fun j => (F.R j).length)).sum)+
      2*[core,halo,header].length+1 = 4*D+2*B+7 := by
    simp [F,H,M,masterLoaded,hoc.symm,hoh.symm,hohead.symm,
      ‹core ≠ halo›,‹core ≠ header›,‹halo ≠ header›,length_binSyms]; omega
  rw [hcost] at he
  have hend : {F with R := fun j => if j ∈ [core,halo,header] then [] else F.R j} =
      {S with R := Function.update S.R output ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j ∈ [core,halo,header]
    · have hjo : j ≠ output := (hout j hj).symm
      simp only [ite_eq_left hj,Function.update_of_ne hjo]
      exact (hblank j hj).symm
    · have hjc : j ≠ core := by intro hh; exact hj (by simp [hh])
      have hjh : j ≠ halo := by intro hh; exact hj (by simp [hh])
      have hjhead : j ≠ header := by intro hh; exact hj (by simp [hh])
      simp [F,H,M,masterLoaded,hj,Function.update_apply,hjc,hjh,hjhead]
  rw [hend] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _
    (by simp only [Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
