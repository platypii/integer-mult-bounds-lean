module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTile
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTilePlanStock

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q c d W K N : ℕ}

noncomputable def conditionalStockAllowance (plan : ArchiveTilePlan t₀ T Q c d W) (N : ℕ) : ℕ :=
  if N = 0 then 0 else plan.stockAllowance

theorem conditional_exec_within {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (active : Fin T) (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K)
    (hW : 0 < N → 0 < W) (L w : ℕ) (hpacket : W = L*w) (hN : N ≤ (2^d)^c)
    (rows : Fin N → Fin (2^d) → List GaussianInt) (hlen : ∀ i j, (rows i j).length = L)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (hready : plan.Ready w rows S)
    (hactive : (S.R active).head?.isSome = decide (0 < N)) (depth : ℕ) :
    ∃ result : Result L rows, result.capacity = capacity N ((2^d)^c) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ plan.conditionalCost N S ∧
        ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
          plan.conditionalStockAllowance N) depth (plan.conditionalProgram active) (Host.mk v S) n
          (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
            ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => result.padded i j).flatten).flatten))}) := by
  let v₀ : HS T Q (prime+K) U := {v with flag := (S.R active).head?.isSome}
  let Inv := fun z (state : Store (HΓ (T := T) (prime+K)) (HS T Q (prime+K) U)) =>
    mnSize state+z ≤ mnSize (Host.mk v S)+depth+plan.conditionalStockAllowance N
  have hpeek : ExecWithin body Inv depth (.act (peekR active)) (Host.mk v S) 1 (Host.mk v₀ S) := by
    have he := mn_native_exec_within (Exec.act (body := body) (peekR active) (Host.mk v S)) 0
      (by simp [peekR,mnActPush,mnNativePushBound]) depth
      (mnSize (Host.mk v S)+depth+plan.conditionalStockAllowance N)
      (by simpa only [Nat.zero_mul,Nat.add_zero] using (Nat.le_add_right
        (mnSize (Host.mk v S)+depth) (plan.conditionalStockAllowance N)))
    simpa only [peekR_run,v₀] using he
  by_cases hz : N = 0
  · subst N
    let padded : Fin 0 → Fin (2^d) → List GaussianInt := fun i => Fin.elim0 i
    have hsrc : S.R plan.src = [] := by simpa using hready.hsrc
    have hleft : (fun _ : Fin T => ([] : List (Fin (prime+K+4)))) = S.L := by
      funext i; exact (hready.hL i).symm
    have hupdate : Function.update S.R plan.src [] = S.R := by
      rw [←hsrc]; exact Function.update_eq_self _ _
    have hflag : v₀.flag = false := by simpa [v₀] using hactive
    have hd : ExecWithin body Inv depth (.act .done) (Host.mk v₀ S) 1 (Host.mk v₀ S) := by
      simpa only [Action.run] using ExecWithin.act (body := body) .done (Host.mk v₀ S) hpeek.final hpeek.final
    let result : Result L rows := ⟨0,by omega,padded,(by intro i; exact Fin.elim0 i),(by intro i; exact Fin.elim0 i)⟩
    refine ⟨result,rfl,v₀,3,rfl,by simp [conditionalCost],?_⟩
    have he := ExecWithin.seq hpeek (ExecWithin.cond_false (p := plan.program) hflag hd)
    simpa [conditionalProgram,result,padded,hleft,hupdate] using he
  · have hpos : 0 < N := Nat.pos_of_ne_zero hz
    obtain ⟨padded,hp,hr,v₁,n₁,hu₁,hn₁,he₁⟩ := plan.exec_within body hA (hW hpos) L w hpacket hN rows hlen v₀ S hready depth
    have hflag : v₀.flag = true := by simpa [v₀,hpos] using hactive
    have hsize : mnSize (Host.mk v₀ S) = mnSize (Host.mk v S) := by
      rw [mnSize_mk_registerBankStock,mnSize_mk_registerBankStock]
    have hw := he₁.mono (J := Inv) (by
      intro z state hs
      simpa only [Inv,conditionalStockAllowance,hz,ite_false,hsize] using hs)
    have he := ExecWithin.seq hpeek (ExecWithin.cond_true (q := .act .done) hflag hw)
    exact ⟨⟨(2^d)^c,hN,padded,hp,hr⟩,by simp [capacity,hz],v₁,1+(n₁+1),hu₁,
      by simp only [conditionalCost,hz,ite_false]; omega,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
