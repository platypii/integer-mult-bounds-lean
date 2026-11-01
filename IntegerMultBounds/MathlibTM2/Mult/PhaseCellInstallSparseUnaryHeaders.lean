module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies

/-! Structural installation of a sparse unary bank around one live payload.
The same copier proof supports full recovery headers and seed headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem installSparseUnaryHeaders_exec (ports : List (Fin N)) (hports : ports.Nodup)
    (payload : Fin N) (hpayloadOff : payload ∉ ports) (σ : Fin N → ℕ)
    (hzero : ∀ i, i ∉ ports → σ i = 0)
    (source work : Fin N → Fin T) (hwork : Function.Injective work) (tmp : Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hworkTmp : ∀ i, work i ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i ∈ ports, (S.R (source i)).length = σ i)
    (hblank : ∀ i, i ≠ payload → S.R (work i) = [])
    (xs : List (Fin (A+4))) (hpayload : S.R (work payload) = xs) (htmp : S.R tmp = []) :
    let rs := ports.map (fun k => (source k,work k))
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) rs
    let F : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R rs}
    ∃ v', v'.user = v.user ∧
      (∀ i, F.R (work i) = if i = payload then xs else List.replicate (σ i) tick) ∧
      (∀ k, (∀ i, k ≠ work i) → F.R k = S.R k) ∧
      Exec body (copyUnaryHeaders tmp rs) (Host.mk v S) cost (Host.mk v' F) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*cost) depth
        (copyUnaryHeaders tmp rs) (Host.mk v S) cost (Host.mk v' F) := by
  dsimp only
  let rs := ports.map (fun k => (source k,work k))
  let value := fun k => (S.R k).length
  let F : Stacks T A := {S with R := unaryCopiesR value S.R rs}
  have hnd : (rs.map Prod.snd).Nodup := by
    simp only [rs,List.map_map,Function.comp_def]
    exact List.Nodup.map hwork hports
  obtain ⟨v',hu,he⟩ := copyUnaryHeaders_exec (body := body) tmp rs (by
    intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    have hsw := hsourceOff i i
    have hst := hsourceTmp i
    have hwt := hworkTmp i
    simp_all) (by
    intro r hr p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    exact (hsourceOff j i).symm) value v S (by intro r hr; rfl) htmp
  have hready (i : Fin N) : F.R (work i) =
      if i = payload then xs else List.replicate (σ i) tick := by
      change unaryCopiesR value S.R rs (work i) = _
      by_cases hi : i ∈ ports
      · have h124 : i ≠ payload := by
          intro heq
          subst i
          exact hpayloadOff hi
        have hm : (source i,work i) ∈ rs := List.mem_map.mpr ⟨i,hi,rfl⟩
        rw [unaryCopiesR_at value S.R rs hnd _ hm,ite_eq_right h124,hblank i h124,List.append_nil]
        exact congrArg (fun N => List.replicate N tick) (hvalues i hi)
      · have hoff : ∀ p ∈ rs, p.2 ≠ work i := by
          intro p hp heq
          obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
          exact hi (hwork heq ▸ hj)
        rw [unaryCopiesR_off value S.R rs (work i) hoff]
        by_cases h124 : i = payload
        · subst i; simpa only [ite_true] using hpayload
        · rw [ite_eq_right h124,hzero i hi,List.replicate_zero]
          exact hblank i h124
  have hframe (k : Fin T) (hk : ∀ i, k ≠ work i) : F.R k = S.R k := by
    apply unaryCopiesR_off
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact (hk i).symm
  refine ⟨v',hu,hready,hframe,he,fun depth => ?_⟩
  exact mn_native_exec_within he 2 (copyUnaryHeaders_native _ _) depth _ (by dsimp only [value,rs]; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
