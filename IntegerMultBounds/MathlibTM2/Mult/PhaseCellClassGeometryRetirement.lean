module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassGeometryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Retire the four loaded numerical geometry words, preserving the computed
result and restoring the initially fresh bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type}

theorem classGeometryLoadCost_eq (bank : ComputedClassBank → Fin T) (src : Fin 4 → Fin T)
    (S : Stacks T A) (B : ℕ) (hwords : ∀ i, (S.R (src i)).length = B) :
    ((classGeometryCopies bank src).map (fun r => 6*(S.R r.1).length+6)).sum+1 = 24*B+25 := by
  simp [classGeometryCopies,classGeometryAssignments,hwords]
  omega

theorem retireClassGeometry_exec_within (body : P → Pr P T Q A U)
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank) (src : Fin 4 → Fin T)
    (k : Fin T) (hoff : ∀ i, geometry bank i ≠ k) (ys : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, i ≠ .control .source → S.R (bank i) = [])
    (B : ℕ) (hwords : ∀ i, (S.R (src i)).length = B) (depth : ℕ) :
    let M := loadedClassGeometry bank src S
    let F : Stacks T A := {M with R := Function.update M.R k ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v F)+depth+0) depth
        (clearWords ((classGeometryCopies bank src).map Prod.snd)) (Host.mk v F) (8*B+9)
        (Host.mk v' {S with R := Function.update S.R k ys}) := by
  dsimp only
  let M := loadedClassGeometry bank src S
  let F : Stacks T A := {M with R := Function.update M.R k ys}
  let regs := (classGeometryCopies bank src).map Prod.snd
  have hnd : regs.Nodup := classGeometryCopies_nodup bank hinj src
  have hsep (r) (hr : r ∈ classGeometryCopies bank src) : r.2 ≠ k := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact hoff p.2
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) regs hnd v F
  have hvolume : (regs.map (fun j => (F.R j).length)).sum = 4*B := by
    have hh : (regs.map (fun j => (F.R j).length)).sum =
        ((classGeometryCopies bank src).map (fun r => (S.R r.1).length)).sum := by
      simp only [regs,List.map_map]
      congr 1
      apply List.map_congr_left
      intro r hr
      change (F.R r.2).length = (S.R r.1).length
      rw [show F.R r.2 = M.R r.2 from Function.update_of_ne (hsep r hr) _ _]
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      exact congrArg List.length (loadedClassGeometry_read bank hinj src S hblank p hp)
    rw [hh]
    simp [classGeometryCopies,classGeometryAssignments,hwords]
    omega
  have hlen : regs.length = 4 := by simp [regs,classGeometryCopies,classGeometryAssignments]
  rw [hvolume,hlen] at he
  have htime : 2*(4*B)+2*4+1 = 8*B+9 := by omega
  rw [htime] at he
  have hend : {F with R := fun j => if j ∈ regs then [] else F.R j} = {S with R := Function.update S.R k ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j ∈ regs
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hj
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      have hz : S.R (geometry bank p.2) = [] := hblank _ (by simp)
      simp only [if_pos hj,Function.update_of_ne (hoff p.2),hz]
    · have hM : M.R j = S.R j := copyWordHeadersR_off S.R (classGeometryCopies bank src) S.R j
        (by intro r hr he; exact hj (List.mem_map.mpr ⟨r,hr,he⟩))
      simp [hj,F,hM,Function.update_apply]
  rw [hend] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _
    (by simp only [F,M,Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
