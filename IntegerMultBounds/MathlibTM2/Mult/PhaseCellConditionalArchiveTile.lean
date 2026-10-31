module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTilePlan

/-! Empty classes have zero capacity and no transpose work. A retained runtime
header selects the existing tile executor only for nonempty classes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q c d W K N : ℕ}

def capacity (N C : ℕ) := if N = 0 then 0 else C

theorem le_capacity {N C : ℕ} (hN : N ≤ C) : N ≤ capacity N C := by
  by_cases h : N = 0 <;> simp [capacity,h,hN]

noncomputable def conditionalProgram {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (active : Fin T) : Pr P T Q (prime+K) U :=
  .seq (.act (peekR active)) (.cond (·.flag) plan.program (.act .done))

noncomputable def conditionalCost (plan : ArchiveTilePlan t₀ T Q c d W)
    (N : ℕ) (S : Stacks T (prime+K)) := if N = 0 then 3 else plan.cost S+2

structure Result {N B : ℕ} (L : ℕ) (rows : Fin N → Fin B → List GaussianInt) where
  capacity : ℕ
  capacity_ge : N ≤ capacity
  padded : Fin capacity → Fin B → List GaussianInt
  rowLength : ∀ i j, (padded i j).length = L
  realRows : ∀ i j, padded (paddedCoreIndex capacity_ge i) j = rows i j

theorem conditional_exec {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (active : Fin T) (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K)
    (hW : 0 < N → 0 < W) (L w : ℕ) (hpacket : W = L*w) (hN : N ≤ (2^d)^c)
    (rows : Fin N → Fin (2^d) → List GaussianInt) (hlen : ∀ i j, (rows i j).length = L)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (hready : plan.Ready w rows S)
    (hactive : (S.R active).head?.isSome = decide (0 < N)) :
    ∃ result : Result L rows, result.capacity = capacity N ((2^d)^c) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ plan.conditionalCost N S ∧
        Exec body (plan.conditionalProgram active) (Host.mk v S) n
          (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
            ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => result.padded i j).flatten).flatten))}) := by
  let v₀ : HS T Q (prime+K) U := {v with flag := (S.R active).head?.isSome}
  have hpeek : Exec body (.act (peekR active)) (Host.mk v S) 1 (Host.mk v₀ S) := by
    simpa only [peekR_run,v₀] using Exec.act (body := body) (peekR active) (Host.mk v S)
  by_cases hz : N = 0
  · subst N
    let padded : Fin 0 → Fin (2^d) → List GaussianInt := fun i => Fin.elim0 i
    have hsrc : S.R plan.src = [] := by simpa using hready.hsrc
    have hleft : (fun _ : Fin T => ([] : List (Fin (prime+K+4)))) = S.L := by
      funext i; exact (hready.hL i).symm
    have hupdate : Function.update S.R plan.src [] = S.R := by
      rw [←hsrc]; exact Function.update_eq_self _ _
    have hflag : v₀.flag = false := by simpa [v₀] using hactive
    have hd : Exec body (.act .done) (Host.mk v₀ S) 1 (Host.mk v₀ S) := by
      simpa [Action.run] using Exec.act (body := body) .done (Host.mk v₀ S)
    let result : Result L rows := ⟨0,by omega,padded,(by intro i; exact Fin.elim0 i),(by intro i; exact Fin.elim0 i)⟩
    refine ⟨result,rfl,v₀,3,rfl,by simp [conditionalCost],?_⟩
    have he := Exec.seq hpeek (Exec.cond_false (p := plan.program) hflag hd)
    simpa [conditionalProgram,result,padded,hleft,hupdate] using he
  · have hpos : 0 < N := Nat.pos_of_ne_zero hz
    obtain ⟨padded,hp,hr,v₁,n₁,hu₁,hn₁,he₁⟩ := plan.exec body hA (hW hpos) L w hpacket hN rows hlen v₀ S hready
    have hflag : v₀.flag = true := by simpa [v₀,hpos] using hactive
    have he := Exec.seq hpeek (Exec.cond_true (q := .act .done) hflag he₁)
    exact ⟨⟨(2^d)^c,hN,padded,hp,hr⟩,by simp [capacity,hz],v₁,1+(n₁+1),hu₁,
      by simp only [conditionalCost,hz,ite_false]; omega,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
