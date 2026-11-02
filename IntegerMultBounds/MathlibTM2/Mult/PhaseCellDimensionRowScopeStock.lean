module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDimensionRowScope
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Read, use and release one row of changing dimension masters. The owned
payload may change while the row and every spectator are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem withDimensionRow_exec_within (width zero queue binary duplicate work saved tmp payload : Fin T)
    (V : ℕ) (xs : List (ℕ × Fin T))
    (hreg : ∀ p ∈ xs, [width,zero,queue,binary,p.2,duplicate,work,saved,tmp].Nodup)
    (hds : (xs.map Prod.snd).Nodup) (hfit : ∀ p ∈ xs, p.1 < 2^V)
    (hpayload : ∀ p ∈ xs, p.2 ≠ payload) (hqueue : ∀ p ∈ xs, p.2 ≠ queue)
    (tail output : List (Fin (A+4))) (run : Pr P T Q A U) (C reserve depth : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hzero : S.R zero = [])
    (hsource : S.R queue = (xs.flatMap fun p => binSyms V p.1)++tail)
    (hblank : ∀ k ∈ [binary,duplicate,work,saved,tmp]++xs.map Prod.snd, S.R k = [])
    (hrun : ∀ vi : HS T Q A U, ∃ vf n, vf.user = vi.user ∧ n ≤ C ∧
      ExecWithin body (fun d state => mnSize state+d ≤
        mnSize (Host.mk vi (dimensionRowState xs queue tail S))+depth+reserve) depth
        run (Host.mk vi (dimensionRowState xs queue tail S)) n
        (Host.mk vf {(dimensionRowState xs queue tail S) with L := (fun _ => []), R := (Function.update (dimensionRowState xs queue tail S).R payload output)})) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ readDimensionRowCost V xs+C+(2*(xs.map Prod.fst).sum+2*xs.length+1) ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        3*readDimensionRowCost V xs+reserve) depth (withDimensionRow width zero queue binary duplicate work saved tmp (xs.map Prod.snd) run)
        (Host.mk v S) n (Host.mk v' {S with L := (fun _ => []), R :=
          (Function.update (Function.update S.R queue tail) payload output)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readDimensionRow_exec_within (body := body) width zero queue binary duplicate work saved tmp
    V xs hreg hds hfit tail v S hwidth hzero hsource hblank depth
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hrun v₁
  let F : Stacks T A := {S with L := (fun _ => []), R :=
    (Function.update (Function.update S.R queue tail) payload output)}
  have hblankF : ∀ k ∈ xs.map Prod.snd, F.R k = [] := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hk
    simp only [F,Function.update_of_ne (hpayload p hp),Function.update_of_ne (hqueue p hp)]
    exact hblank _ (List.mem_append_right _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  obtain ⟨v₃,hu₃,he₃⟩ := releaseDimensionRow_exec xs hds v₂ F hblankF
  have hstart : {(dimensionRowState xs queue tail S) with L := (fun _ => []), R := (Function.update (dimensionRowState xs queue tail S).R payload output)} =
      {F with R := dimensionRowR xs F.R} := by
    refine Stacks.ext rfl rfl rfl ?_
    exact (dimensionRowR_update_off xs (Function.update S.R queue tail) payload output hpayload).symm
  rw [hstart] at he₂
  let bound := mnSize (Host.mk v S)+depth+3*readDimensionRowCost V xs+reserve
  have hsetup := he₁.final
  change mnSize (Host.mk v₁ (dimensionRowState xs queue tail S))+depth ≤
    mnSize (Host.mk v S)+depth+3*readDimensionRowCost V xs at hsetup
  have hw₁ := he₁.mono (J := fun d state => mnSize state+d ≤ bound) (by
    intro d state hs
    dsimp only [bound]
    omega)
  have hw₂ := he₂.mono (J := fun d state => mnSize state+d ≤ bound) (by
    intro d state hs
    dsimp only [bound]
    omega)
  have hw₃ := mn_native_exec_within he₃ 0 (clearWords_native (xs.map Prod.snd))
    depth bound (by have hh := hw₂.final; omega)
  refine ⟨v₃,n₁+(n₂+(2*(xs.map Prod.fst).sum+2*xs.length+1)),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · omega
  · exact ExecWithin.seq hw₁ (ExecWithin.seq hw₂ hw₃)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
