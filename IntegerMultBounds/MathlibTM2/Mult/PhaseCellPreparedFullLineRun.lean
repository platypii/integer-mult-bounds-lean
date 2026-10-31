module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineProducer
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineInputPlan
public import IntegerMultBounds.MathlibTM2.Host.ClearBankExcept

/-! An ordinary full-period RHS batch generates its bank, executes S3 once,
and retires every generated word except the borrowed scalar-width seed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def Compatible (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q) : Prop :=
  ∀ i k, k ∈ producer.support++[producer.result] → input.work i ≠ k

noncomputable def run (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
    (recovery : Bool) : Pr P T Q A U :=
  .seq input.generate (.seq (producer.fullLineFromLiveBank input.work recovery)
    (clearBankExcept input.work (familyInverseScalarReg .wr)))

private theorem stock_drop_zero (base depth setup stock x : ℕ)
    (h : x ≤ base+depth+(setup+(stock+0))) : x ≤ base+depth+(setup+stock) := by omega

theorem run_exec (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q)
    (hcompat : input.Compatible producer) (recovery : Bool) (hA : 96 ≤ A)
    {p u l target t : ℕ} [NeZero t] {d : ℝ}
    (hp : 4 ≤ p) (hst : s < t) (hu : 1 ≤ u) (hwidth : 8*p ≤ 2^u)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : (u : ℝ)*d ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) (htarget : p+2 ≤ target)
    (Fs : List (ZMod s → GaussianInt)) (hFs : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (X F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (u : ℝ)) = 1)
    (v : HS T Q A U) (S : Stacks T A) (hready : input.Ready p u l target t Fs S)
    (hblank : ∀ i, S.R (producer.gridWork i) = [])
    (hleft : ∀ i, S.L (producer.gridWork (familyInverseCoreReg i)) = [])
    (hcontrols : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock], S.R k = [])
    (C : ℕ) (hpush : mnProgPush (producer.gridProgram (P := P) (U := U) (A := A) recovery) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) (depth : ℕ) :
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    ∃ v' n output, v'.user = v.user ∧
      n ≤ setupTime p u l target s t Fs.length+
        ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607)) ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r))) depth
        (input.run producer recovery) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R producer.result (output++S.R producer.result)}) := by
  dsimp only
  let r := fullLineGridRecord (A := A) p u l target t Fs
  have hr := fullLineGridRecord_ready (A := A) p u l target t hu hwidth hbudget hband hpad Fs hFs
  have hreg := producer.hreg
  regs_ne hreg
  have hport (k : Fin T)
      (hk : k ∈ [producer.src,producer.saved,producer.count,producer.tmp,producer.spare,producer.clock,producer.savedClock,producer.result]) :
      ∀ i, k ≠ input.work i := by
    intro i he
    exact hcompat i k (producer.control_mem k hk) he.symm
  have hworkOff (i : Fin 303) : ∀ j, producer.gridWork i ≠ input.work j := by
    intro j he
    apply hcompat j (producer.gridWork i)
    · apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_ofFn.mpr ⟨Fin.castLE (by decide : 303 ≤ 325) i,rfl⟩
    · exact he.symm
  obtain ⟨v₁,n₁,M,hu₁,hn₁,hwords,hframe,hI,hO,hL,he₁⟩ := input.generate_exec p u l target t hst Fs v S hready depth
  have hsourceReg : ∀ i, [input.work i,producer.src,producer.tmp,producer.saved].Nodup := by
    intro i
    have hs := (hport producer.src (by simp) i).symm
    have ht := (hport producer.tmp (by simp) i).symm
    have hv := (hport producer.saved (by simp) i).symm
    regs_nodup
  have hblankM (i : Fin 303) : M.R (producer.gridWork i) = [] :=
    (hframe _ (hworkOff i)).trans (hblank i)
  have hcontrolsM : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock], M.R k = [] := by
    intro k hk
    have hh := hcontrols k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact (hframe _ (hport _ (by simp))).trans hh
  obtain ⟨v₂,n₂,output,hu₂,hn₂,hproduced,he₂⟩ := producer.fullLineFromLiveBank_exec
    input.work hsourceReg recovery hA hp hst hθ hgap r hr rfl rfl htarget X Y hX hY J hJ v₁ M hwords hblankM
    (by intro i; rw [hL]; exact hleft i)
    (by
      intro k hk
      have hm : k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp
      exact hcontrolsM k hm)
    (hcontrolsM _ (by simp)) (hcontrolsM _ (by simp)) (hcontrolsM _ (by simp)) C hpush hbody depth
  have hresultOff : ∀ i, producer.result ≠ input.work i := hport producer.result (by simp)
  have hresultM : M.R producer.result = S.R producer.result := hframe _ hresultOff
  let F : Stacks T A := {M with R := Function.update M.R producer.result (output++M.R producer.result)}
  let base := Function.update S.R producer.result (output++S.R producer.result)
  have hFwords (i : Fin 303) : F.R (input.work i) = r.words i := by
    rw [show F.R (input.work i) = M.R (input.work i) from Function.update_of_ne (hresultOff i).symm _ _]
    exact hwords i
  have hbaseBank (i : Fin 303) : base (input.work i) = S.R (input.work i) :=
    Function.update_of_ne (hresultOff i).symm _ _
  have hscalar : r.words (familyInverseScalarReg .wr) =
      List.replicate (inverseCallerWordWidth p u l target s t) tick := hr.scalars .wr
  have hkeep : F.R (input.work (familyInverseScalarReg .wr)) = base (input.work (familyInverseScalarReg .wr)) := by
    rw [hFwords,hbaseBank,hscalar,hready.width]
  have hbaseBlank (i : Fin 303) (hi : i ≠ familyInverseScalarReg .wr) : base (input.work i) = [] :=
    (hbaseBank i).trans (hready.blank i hi)
  have hbaseFrame (k : Fin T) (hk : ∀ i, k ≠ input.work i) : F.R k = base k := by
    by_cases hr : k = producer.result
    · subst k; simp only [F,base,Function.update_self,hresultM]
    · simp only [F,base,Function.update_of_ne hr]
      exact hframe k hk
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := clearBankExcept_exec (body := body) input.work input.injective
    (familyInverseScalarReg .wr) base v₂ F hkeep hbaseBlank hbaseFrame depth
  simp only [hFwords] at hn₃
  have htime := Nat.add_le_add hn₁ (Nat.add_le_add hn₂ hn₃)
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add (b := 0) he₂ he₃)
  have hfinal : {F with R := base} = {S with R := Function.update S.R producer.result (output++S.R producer.result)} :=
    Stacks.ext hI hO hL rfl
  rw [hfinal] at hwhole
  refine ⟨v₃,n₁+(n₂+n₃),output,hu₃.trans (hu₂.trans hu₁),htime,hproduced,?_⟩
  exact hwhole.mono (by intro d z hz; exact stock_drop_zero _ _ _ _ _ hz)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan
