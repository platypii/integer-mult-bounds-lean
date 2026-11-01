module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexRecoveryHeaders

/-! Retained ordinary metadata and an exposed payload install the exact complex
recovery input bank. Sources are borrowed and scratch is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def complexRecoveryHeaderCopies (source work : Fin 392 → Fin T) : List (Fin T × Fin T) :=
  complexRecoveryHeaderPorts.map (fun k => (source k,work k))

def installComplexRecoveryHeaders (source work : Fin 392 → Fin T) (tmp : Fin T) : Pr P T Q A U :=
  copyUnaryHeaders tmp (complexRecoveryHeaderCopies source work)

theorem installComplexRecoveryHeaders_exec (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (source work : Fin 392 → Fin T)
    (hwork : Function.Injective work) (tmp : Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hworkTmp : ∀ i, work i ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i ∈ complexRecoveryHeaderPorts,
      (S.R (source i)).length = complexRecoveryHeader H W Fs.length i)
    (hblank : ∀ i, i ≠ 124 → S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hpayload : S.R (work 124) = cstream A W (Fs.map (packedInterval H.origin H.span)).flatten)
    (htmp : S.R tmp = []) :
    let rs := complexRecoveryHeaderCopies source work
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) rs
    let F : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R rs}
    ∃ v', v'.user = v.user ∧ embStk work F = complexRecoveryInput H W Fs S.inp S.out ∧
      (∀ k, (∀ i, k ≠ work i) → F.R k = S.R k) ∧
      Exec body (installComplexRecoveryHeaders source work tmp) (Host.mk v S) cost (Host.mk v' F) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*cost) depth
        (installComplexRecoveryHeaders source work tmp) (Host.mk v S) cost (Host.mk v' F) := by
  dsimp only
  let rs := complexRecoveryHeaderCopies source work
  let value := fun k => (S.R k).length
  let F : Stacks T A := {S with R := unaryCopiesR value S.R rs}
  have hnd : (rs.map Prod.snd).Nodup := by
    simp only [rs,complexRecoveryHeaderCopies,List.map_map,Function.comp_def]
    exact List.Nodup.map hwork (by decide : complexRecoveryHeaderPorts.Nodup)
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
  have hbank : embStk work F = complexRecoveryInput H W Fs S.inp S.out := by
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      exact hleft i
    · funext i
      change unaryCopiesR value S.R rs (work i) = _
      rw [complexRecoveryInput_right]
      by_cases hi : i ∈ complexRecoveryHeaderPorts
      · have h124 : i ≠ 124 := by
          intro heq
          subst i
          exact (by decide : (124 : Fin 392) ∉ complexRecoveryHeaderPorts) hi
        have hm : (source i,work i) ∈ rs := List.mem_map.mpr ⟨i,hi,rfl⟩
        rw [unaryCopiesR_at value S.R rs hnd _ hm,ite_eq_right h124,hblank i h124,List.append_nil]
        exact congrArg (fun N => List.replicate N tick) (hvalues i hi)
      · have hoff : ∀ p ∈ rs, p.2 ≠ work i := by
          intro p hp heq
          obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
          exact hi (hwork heq ▸ hj)
        rw [unaryCopiesR_off value S.R rs (work i) hoff]
        by_cases h124 : i = 124
        · subst i; simpa only [ite_true] using hpayload
        · rw [ite_eq_right h124,complexRecoveryHeader_off H W Fs.length i hi,List.replicate_zero]
          exact hblank i h124
  have hframe (k : Fin T) (hk : ∀ i, k ≠ work i) : F.R k = S.R k := by
    apply unaryCopiesR_off
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact (hk i).symm
  refine ⟨v',hu,hbank,hframe,he,fun depth => ?_⟩
  exact mn_native_exec_within he 2 (copyUnaryHeaders_native _ _) depth _ (by dsimp only [value,rs]; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
