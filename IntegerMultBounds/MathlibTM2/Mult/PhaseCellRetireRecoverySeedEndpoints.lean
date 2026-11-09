module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadRecoverySeedEndpoints
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Retire the two changing seed words after the numerical callback. The base
state may already contain the consumed queue, remaining payload and new output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def recoverySeedEndpointState (source : Fin 392 → Fin T) (x y : ℕ) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R (source 111) (List.replicate x tick))
    (source 113) (List.replicate y tick))}

/-- Updates to payload, queue or output registers commute with the live seeds. -/
theorem recoverySeedEndpointState_updateR (source : Fin 392 → Fin T) (x y : ℕ)
    (S : Stacks T A) (r : Fin T) (word : List (Fin (A+4)))
    (ha : r ≠ source 111) (hb : r ≠ source 113) :
    {(recoverySeedEndpointState source x y S) with R :=
      (Function.update (recoverySeedEndpointState source x y S).R r word)} =
      recoverySeedEndpointState source x y {S with R := Function.update S.R r word} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hr : i = r <;> by_cases hia : i = source 111 <;> by_cases hib : i = source 113 <;>
    simp_all [recoverySeedEndpointState]

def retireRecoverySeedEndpoints (source : Fin 392 → Fin T) : Pr P T Q A U :=
  clearWords [source 111,source 113]

/-- Clearing the generated endpoint words restores the base state exactly and
never increases stock, even when the caller retains output in that base state. -/
theorem retireRecoverySeedEndpoints_exec (source : Fin 392 → Fin T)
    (hsep : source 111 ≠ source 113) (x y : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (ha : S.R (source 111) = []) (hb : S.R (source 113) = []) (depth : ℕ) :
    let E := recoverySeedEndpointState source x y S
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v E)+depth) depth
        (retireRecoverySeedEndpoints source) (Host.mk v E) (2*(x+y)+5) (Host.mk v' S) := by
  dsimp only
  let E := recoverySeedEndpointState source x y S
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [source 111,source 113]
    (by simp [hsep]) v E
  have hcost : 2*(([source 111,source 113].map fun r => (E.R r).length).sum)+
      2*([source 111,source 113] : List (Fin T)).length+1 = 2*(x+y)+5 := by
    simp [E,recoverySeedEndpointState,hsep]
  have hfinal : {E with R := fun k => if k ∈ [source 111,source 113] then [] else E.R k} = S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hka : k = source 111 <;> by_cases hkb : k = source 113 <;>
      simp_all [E,recoverySeedEndpointState]
  rw [hcost,hfinal] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _ (by simp only [Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
