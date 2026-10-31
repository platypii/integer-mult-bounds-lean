module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedProducer
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Generate a packed job's actual bank, then execute its descriptor lifecycle
and numerical producer. Ordinary retained headers replace all prepared words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace SupplierInputPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def run (input : SupplierInputPlan T) (producer : PackedProducerPlan T Q) : Pr P T Q A U :=
  .seq (input.produce producer) (clearWords (List.ofFn input.work))

theorem run_exec (input : SupplierInputPlan T) (producer : PackedProducerPlan T Q)
    (r : PackedNormalizedJob A s)
    (hsourceReg : ∀ i, [input.work i,producer.src,producer.tmp,producer.saved].Nodup)
    (hworkOff : ∀ i j, producer.work i ≠ input.work j)
    (hresultOff : ∀ i, producer.result ≠ input.work i)
    (hcontrolOff : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
      ∀ i, k ≠ input.work i)
    (hA : 96 ≤ A) (t B L : ℕ) [NeZero t] (ht : r.t = t) (hp : 4 ≤ r.p)
    (htarget : r.p+2 ≤ r.targetOut) (hlocal : r.localityTarget = r.targetOut)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1)
    (hreplicas : r.Fs.length = B) (hcore : IntegerMultBounds.NLogN.PhaseCellMatrix.coreLength s r.coreWidth r.k = L)
    (v : HS T Q A U) (S : Stacks T A) (hready : input.Ready r S)
    (hblank : ∀ i, S.R (producer.work i) = []) (hleft : ∀ i, S.L (producer.work i) = [])
    (hscratch : ∀ k ∈ [producer.count,producer.tmp,producer.spare], S.R k = [])
    (hclock : S.R producer.clock = []) (hsaved : S.R producer.saved = []) (hsavedClock : S.R producer.savedClock = [])
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    let tape := descriptorScheduleTape producer.work PackedNormalizedJob.words [r]
    ∃ v' n, ∃ rows : Fin 1 → Fin B → List GaussianInt,
      v'.user = v.user ∧ n ≤ input.timeCost r S+(producer.timeCost (U := U) [r]+20*tape.length+7)+
        (2*(∑ i, (r.words i).length)+651) ∧
      (∀ i j, (rows i j).length = L) ∧
      (∀ i : Fin 1, r.ExactRowOutput J (List.ofFn (rows i))) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (input.stock r S+(31*tape.length+9+(C+1)*producer.workspace (U := U) [r]))) depth
        (input.run producer) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R producer.result
          ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++S.R producer.result))}) := by
  dsimp only
  obtain ⟨v₁,n₁,F,rows,hu₁,hn₁,hlen,hrows,hwords,hframe,hL,hI,hO,he₁,hresult⟩ := input.produce_exec (body := body)
    producer r hsourceReg hworkOff hresultOff hcontrolOff hA t B L ht hp htarget hlocal J hJ hreplicas hcore
    v S hready hblank hleft hscratch hclock hsaved hsavedClock C depth hpush hbody
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) (List.ofFn input.work)
    (List.nodup_ofFn_ofInjective input.injective) v₁ F
  have hcost : 2*((List.ofFn input.work).map (fun i => (F.R i).length)).sum+2*(List.ofFn input.work).length+1 =
      2*(∑ i, (r.words i).length)+651 := by
    simp only [List.map_ofFn,Function.comp_def,hwords,List.sum_ofFn,List.length_ofFn]
  rw [hcost] at he₂
  have hw₂ := mn_native_exec_within he₂ 0 (clearWords_native (List.ofFn input.work)) depth _ (by
    simpa only [Nat.zero_mul,Nat.add_zero] using he₁.final)
  have hwhole := ExecWithin.seq he₁ hw₂
  have hout : Host.mk v₂ {F with R := fun i => if i ∈ List.ofFn input.work then [] else F.R i} =
      Host.mk v₂ {S with R := (Function.update S.R producer.result
        ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++S.R producer.result))} := by
    apply congrArg (Host.mk v₂)
    refine Stacks.ext hI hO hL ?_
    funext i
    by_cases hi : i = producer.result
    · subst i
      have hoff : producer.result ∉ List.ofFn input.work := by
        intro hm
        obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
        exact hresultOff j hj.symm
      simpa only [hoff,ite_false,Function.update_self] using hresult
    by_cases hm : i ∈ List.ofFn input.work
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm
      have hm' : input.work j ∈ List.ofFn input.work := List.mem_ofFn.mpr ⟨j,rfl⟩
      simp only [hm',ite_true,Function.update_of_ne hi]
      exact (hready.blank j).symm
    · have hoff : ∀ j, i ≠ input.work j := by
        intro j he
        exact hm (List.mem_ofFn.mpr ⟨j,he.symm⟩)
      simp only [hm,ite_false,Function.update_of_ne hi]
      exact hframe i hi hoff
  rw [hout] at hwhole
  exact ⟨v₂,n₁+(2*(∑ i, (r.words i).length)+651),rows,hu₂.trans hu₁,
    Nat.add_le_add_right hn₁ _,hlen,hrows,hwhole⟩

end SupplierInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
