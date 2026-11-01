module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareDescriptorBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Serialize an owned live bank and retire it. Descriptor data and the clock
remain outside the reusable workspace; all spectators are preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def serializeOwnedDescriptorBank (work : Fin N → Fin T) (dst tmp saved clock : Fin T) : Pr P T Q A U :=
  .seq (prepareDescriptorBank work dst tmp saved clock) (clearWords (List.ofFn work))

def serializedOwnedDescriptorState (work : Fin N → Fin T) (dst clock : Fin T)
    (tape : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update
    (fun k => if k ∈ List.ofFn work then [] else S.R k) dst (tape++S.R dst)) clock (tick::S.R clock))}

private theorem clearWords_pushBound (rs : List (Fin T)) :
    mnNativePushBound 2 (clearWords (P := P) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih => exact ⟨by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush],ih⟩

theorem serializeOwnedDescriptorBank_pushBound (work : Fin N → Fin T) (dst tmp saved clock : Fin T) :
    mnNativePushBound 2 (serializeOwnedDescriptorBank (P := P) (Q := Q) (A := A) (U := U)
      work dst tmp saved clock) := by
  exact ⟨⟨emitDescriptorBank_native _ _ _ _,by simp [mnNativePushBound,mnActPush]⟩,
    clearWords_pushBound _⟩

theorem serializeOwnedDescriptorBank_exec (work : Fin N → Fin T) (hwork : Function.Injective work)
    (dst tmp saved clock : Fin T) (hreg : [dst,tmp,saved,clock].Nodup)
    (hsep : ∀ i, work i ∉ [dst,tmp,saved,clock])
    (v : HS T Q A U) (S : Stacks T A)
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    let tape := descriptorBankTape ((List.ofFn work).map (fun k => (k,S.R k)))
    ∃ v' steps, v'.user = v.user ∧ steps ≤ 13*tape.length+3 ∧
      Exec body (serializeOwnedDescriptorBank work dst tmp saved clock) (mk v S) steps
        (mk v' (serializedOwnedDescriptorState work dst clock tape S)) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(13*tape.length+3)) depth
        (serializeOwnedDescriptorBank work dst tmp saved clock) (mk v S) steps
        (mk v' (serializedOwnedDescriptorState work dst clock tape S)) := by
  dsimp only
  let tape := descriptorBankTape ((List.ofFn work).map (fun k => (k,S.R k)))
  have hr := hreg
  regs_ne hr
  have hports (i : Fin N) : work i ≠ dst ∧ work i ≠ tmp ∧ work i ≠ saved ∧ work i ≠ clock := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  obtain ⟨v₁,hu₁,he₁⟩ := prepareDescriptorBank_prepend_exec (body := body) work dst tmp saved clock
    (by intro i; have hi := hports i; simp_all) ‹dst ≠ clock›.symm v S htmp hsaved 0
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R dst (tape++S.R dst)) clock (tick::S.R clock))}
  have hframe (i : Fin N) : M.R (work i) = S.R (work i) := by
    simp only [M,Function.update_of_ne (hports i).2.2.2,Function.update_of_ne (hports i).1]
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) (List.ofFn work)
    (List.nodup_ofFn.mpr hwork) v₁ M
  have hsum : ((List.ofFn work).map (fun k => (M.R k).length)).sum =
      ((List.ofFn work).map (fun k => (S.R k).length)).sum := by
    simp only [List.map_ofFn,Function.comp_def,hframe]
  have hfinal : {M with R := fun k => if k ∈ List.ofFn work then [] else M.R k} =
      serializedOwnedDescriptorState work dst clock tape S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ List.ofFn work
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
      simp only [serializedOwnedDescriptorState,Function.update_of_ne (hports i).2.2.2,
        Function.update_of_ne (hports i).1,hk,ite_true]
    · by_cases hc : k = clock
      · subst k; simp [serializedOwnedDescriptorState,M,hk]
      · by_cases hd : k = dst
        · subst k; simp [serializedOwnedDescriptorState,M,hk,hc]
        · simp only [serializedOwnedDescriptorState,M,Function.update_of_ne hc,
            Function.update_of_ne hd,hk,ite_false]
  rw [hfinal,hsum,List.length_ofFn] at he₂
  have hlength := descriptorBankTape_length ((List.ofFn work).map (fun k => (k,S.R k)))
  simp only [List.map_map,Function.comp_def,List.length_map,List.length_ofFn] at hlength
  have hcost := emitDescriptorBankCost_le S.R (List.ofFn work)
  let steps := emitDescriptorBankCost S.R (List.ofFn work)+1+
    (2*((List.ofFn work).map (fun k => (S.R k).length)).sum+2*N+1)
  have hn : steps ≤ 13*tape.length+3 := by dsimp only [steps,tape]; omega
  have he : Exec body (serializeOwnedDescriptorBank work dst tmp saved clock) (mk v S) steps
      (mk v₂ (serializedOwnedDescriptorState work dst clock tape S)) := Exec.seq he₁.toExec he₂
  exact ⟨v₂,steps,hu₂.trans hu₁,hn,he,fun depth =>
    mn_native_exec_within he 2 (serializeOwnedDescriptorBank_pushBound _ _ _ _ _) depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
