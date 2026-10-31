module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateInverseParameters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedInverseCaller

/-! Bootstrap the inverse scalar table from retained ordinary headers.
The binary queue is generated, consumed and erased within this execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem inverseParameterState_eq_input (p u l target s t a b : ℕ) :
    inverseParameterState (A := A) p u l target s t a b = inverseInputScalars p u l target s t a b := by
  apply congrArg₂ (fun val acc => (⟨val,acc⟩ : TblSt 25 A))
  · funext i
    fin_cases i <;> rfl
  · exact inverseParameterState_acc p u l target s t a b

private theorem zeroWords_native (width tmp : Fin T) (rs : List (Fin T)) :
    mnNativePushBound 2 (zeroWordBank (P := P) (Q := Q) (A := A) (U := U) width tmp rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    exact ⟨by simp [bzero,zeroBits,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
      mnNativePushBound,mnActPush],ih⟩

private theorem loadWords_native (rg : TblR 25 → Fin T) (queue : Fin T) (is : List (Fin 25)) :
    mnNativePushBound 2 (loadBinaryHeaders (P := P) (Q := Q) (A := A) (U := U) rg queue is) := by
  induction is with
  | nil => exact Nat.zero_le _
  | cons i is ih =>
    exact ⟨by simp [loadBinaryHeader,uclear,takePrefix,transfer,transferAct,scanR,drainR,popDo,keepIn,
      moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush],ih⟩

def generateInverseScalarBank (rg : TblR 25 → Fin T) (source : Fin 8 → Fin T)
    (word saved tmp queue carry : Fin T) : Pr P T Q A U :=
  .seq (generateInverseParameters source (rg .wr) word saved tmp queue carry) (installInverseParameters rg queue)

private theorem scalar_time (x values B : ℕ) (h : x ≤ values*(4*B+10)+8*(8*B+12)+1) :
    x+(164*B+166) ≤ values*(4*B+10)+228*B+263 := by omega

private theorem scalar_stock (x base depth B : ℕ)
    (h : x ≤ base+depth+(8*(2*(4*B+4))+2*(164*B+166))) : x ≤ base+depth+(392*B+396) := by
  have he : 8*(2*(4*B+4))+2*(164*B+166) = 392*B+396 := by ring
  simpa only [he] using h

theorem generateInverseScalarBank_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (source : Fin 8 → Fin T) (word saved tmp queue carry : Fin T)
    (hregs : ∀ i, [source i,rg .wr,word,saved,tmp,queue].Nodup) (hqueueOff : ∀ r, rg r ≠ queue)
    (p u l target s t a b B : ℕ) (hfit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,b] i < 2^B)
    (wl : List (Fin (A+4))) (hwl : wl.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![p,u,l,target,s,t,a,b] i)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ r : TblR 25, r ≠ .wr → S.R (rg r) = [])
    (hscratch : ∀ i ∈ [word,saved,tmp,queue], S.R i = []) (depth : ℕ) :
    ∃ v' n F, v'.user = v.user ∧ n ≤ (p+u+l+target+s+t+a+b)*(4*B+10)+228*B+263 ∧
      tblHolds rg F (tblRho B wl [] (inverseInputScalars p u l target s t a b)) ∧ tblFr rg S F ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(392*B+396)) depth
        (generateInverseScalarBank rg source word saved tmp queue carry) (mk v S) n (mk v' F) := by
  have hB : (S.R (rg .wr)).length = B := by rw [hwidth,hwl]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generateInverseParameters_exec (body := body) source (rg .wr) word saved tmp queue carry
    hregs p u l target s t a b B v S hvalues hB (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> exact hscratch _ (by simp)) depth
  rw [hscratch queue (by simp),List.append_nil] at he₁
  let M : Stacks T A := {S with R := (Function.update S.R queue
    ((inverseParameterWords p u l target s t a b).flatMap (fun r => binSyms B r.2)))}
  have htable (r : TblR 25) : M.R (rg r) = S.R (rg r) := Function.update_of_ne (hqueueOff r) _ _
  obtain ⟨v₂,F,hu₂,he₂,hholds,_,hqueue,hI,hO,hL,hframe⟩ := installInverseParameters_exec (body := body)
    rg hrg queue hqueueOff B p u l target s t a b hfit wl hwl [] v₁ M
    (by rw [htable]; exact hwidth) (by intro r hr; rw [htable]; exact hblank r hr) (by simp [M])
  have hw₂ := mn_native_exec_within he₂ 2 (by
    change mnNativePushBound 2 (.seq (initializeScalarBank rg) (loadBinaryHeaders rg queue [0,1,2,3,4,5,6,7]))
    exact ⟨zeroWords_native _ _ _,loadWords_native _ _ _⟩) depth _ (le_refl _)
  have hwhole := mn_seq_within_add he₁ hw₂
  rw [inverseParameterState_eq_input] at hholds
  refine ⟨v₂,n₁+(164*B+166),F,hu₂.trans hu₁,scalar_time _ _ _ hn₁,hholds,?_,hwhole.mono ?_⟩
  · refine ⟨hI,hO,hL,?_⟩
    intro i hi
    by_cases hq : i = queue
    · subst i; exact hqueue.trans (hscratch queue (by simp)).symm
    · rw [hframe i hq hi]
      exact Function.update_of_ne hq _ _
  · intro d z hz
    exact scalar_stock _ _ _ _ hz

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
