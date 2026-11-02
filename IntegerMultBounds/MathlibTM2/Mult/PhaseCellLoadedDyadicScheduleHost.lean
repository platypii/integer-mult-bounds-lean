module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicScheduleLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedDyadicScheduleStock
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock

/-! Complete physical schedule production from retained binary headers,
including table construction, computed count, publication and cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def loadedDyadicScheduleHost : Pr P 117 Q A U :=
  .seq loadDyadicScheduleInputs generatedDyadicScheduleHost

theorem loadedDyadicScheduleHost_native :
    mnNativePushBound 3 (loadedDyadicScheduleHost (P := P) (Q := Q) (A := A) (U := U)) :=
  ⟨chirpBankLoad_native _ _ _ _,tableCountedPacketHost_native _ _⟩

theorem loadedDyadicScheduleHost_exec (a b C V : ℕ) (hbits : a+b < V)
    (hfit : C*2^(a+b) < 2^V) (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (ha : S.R 97 = binSyms V a) (hb : S.R 98 = binSyms V b) (hC : S.R 102 = binSyms V C)
    (hz : S.R 106 = []) (hwidth : (S.R 115).length = V) (hblank : ∀ r, S.R (originReg r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 110*V+137+32921*(V+1)^5 ∧
      Exec body loadedDyadicScheduleHost (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 109 then
          (dyadicScheduleValues (a+b) a b C).flatMap (binSyms V)++S.R 109 else if r = 116 then
          List.replicate (dyadicStageCount (a+b) a b) tick++S.R 116 else S.R r)}) := by
  obtain ⟨v₁,hu₁,he₁,hh₁⟩ := loadDyadicScheduleInputs_exec (body := body) a b C V hbits hfit v S
    ha hb hC hz hwidth hblank
  let M : Stacks 117 A := {S with R := (chirpBankLoadR originReg dyadicScheduleInput V V
    (dyadicScheduleInputValue a b C) S.R)}
  have hoff (i : Fin 117) (hi : 31 ≤ i.val) : M.R i = S.R i := by
    apply chirpBankLoad_off
    intro r he
    have hr := originReg_range r
    rw [←he] at hr
    omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := generatedDyadicScheduleHost_exec (body := body)
    (dyadicScheduleInitialState a b C)
    (by simp [dyadicScheduleInitialState_value]) (by simp [dyadicScheduleInitialState_value])
    (by simp [dyadicScheduleInitialState_value]) rfl hbits hfit
    (dyadicScheduleInitialState_bounded a b C V hbits hfit) hA v₁ M hh₁
  have ht := hm₂.trans (Cost.dyadicGeneratorPublicationTime_le a b V hbits)
  refine ⟨v₂,110*V+137+m₂,hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
  funext i
  by_cases hi : i.val < 31
  · simp [hi]
  · have hi' : 31 ≤ i.val := by omega
    by_cases h109 : i = 109
    · subst i; simp [hoff 109 (by decide)]
    · by_cases h116 : i = 116
      · subst i; simp [hoff 116 (by decide)]
      · simp [hi,h109,h116,hoff i hi']

theorem loadedDyadicScheduleHost_exec_within (a b C V : ℕ) (hbits : a+b < V)
    (hfit : C*2^(a+b) < 2^V) (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (ha : S.R 97 = binSyms V a) (hb : S.R 98 = binSyms V b) (hC : S.R 102 = binSyms V C)
    (hz : S.R 106 = []) (hwidth : (S.R 115).length = V) (hblank : ∀ r, S.R (originReg r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 110*V+137+32921*(V+1)^5 ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (330*V+411+98763*(V+1)^5)) depth loadedDyadicScheduleHost (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 109 then
          (dyadicScheduleValues (a+b) a b C).flatMap (binSyms V)++S.R 109 else if r = 116 then
          List.replicate (dyadicStageCount (a+b) a b) tick++S.R 116 else S.R r)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := loadedDyadicScheduleHost_exec (body := body) a b C V hbits hfit hA v S
    ha hb hC hz hwidth hblank
  refine ⟨v',m,hu,hm,?_⟩
  intro depth
  exact mn_native_exec_within he 3 loadedDyadicScheduleHost_native depth _ (by nlinarith only [hm])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
