module

public import IntegerMultBounds.MathlibTM2.Fast.CMul
public import IntegerMultBounds.MathlibTM2.Host.WordCmdStock

/-! A single real-coefficient multiplication has a batch-independent reserve.
The compiler's call-free certificate avoids expanding the SS controller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

theorem rmulOne_noCalls (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) :
    WordCmd.NoCalls (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr) := by
  simp [rmulOne,cmulPre,rmulProds,cmulPost,splitP,combP,finP,dpass,selectP,autoInner,
    ssMul,SS.layout,SS.padCopy,SS.readOut,WordCmd.tcompile_noCalls,
    zeroBits,usub,umulSym,scanR,drainR,popDo,moveR,whileR,uclear,WordCmd.NoCalls]

/-- Time bounds only one coefficient's scratch, never the repeated stream. -/
theorem CRuns.exec_within_native {prog : Pr P T Q A U} {ρ ρ' : CR → List (Fin (A+4))}
    {time c : ℕ} (h : CRuns body cr ι prog ρ ρ' time) (hp : mnNativePushBound c prog)
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ time ∧ CHolds cr S' ρ' ∧ CFr cr S S' ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+c*time)
        depth prog (mk v S) n (mk v' S') := by
  obtain ⟨v',S',n,hu,hn,he,hS',hf⟩ := h v S hc hS
  exact ⟨v',S',n,hu,hn,hS',hf,fun depth =>
    mn_native_exec_within he c hp depth _
      (Nat.add_le_add_left (Nat.mul_le_mul_left c hn) _)⟩

end IntegerMultBounds.MathlibTM2.Fast
