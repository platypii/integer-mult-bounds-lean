module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierSetupPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedProducerLifecycle
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputFrame

/-! One fixed supplier body generates its changing numerical headers, solves,
and retires those headers while preserving retained class setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace SupplierSetupPlan
variable {T Q A s : ℕ} [NeZero s] {input : SupplierInputPlan T} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def run (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q) : Pr P T Q A U :=
  .seq plan.program (.seq (input.run producer) (clearWords (numericalRegs input)))

noncomputable def retirementCost (r : PackedNormalizedJob A s) : ℕ :=
  2*((List.ofFn r.factoryMasters).sum+r.V)+23

theorem run_exec (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
    (r : PackedNormalizedJob A s)
    (hsourceReg : ∀ i, [input.work i,producer.src,producer.tmp,producer.saved].Nodup)
    (hworkOff : ∀ i j, producer.work i ≠ input.work j) (hresultInput : producer.result ∉ input.support)
    (hcontrolOff : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
      ∀ i, k ≠ input.work i)
    (hkernelOff : ∀ k ∈ producer.support, (∀ i, input.masters i ≠ k) ∧ k ≠ input.publication.retained 1)
    (hA : 96 ≤ A) (t B L : ℕ) [NeZero t] (ht : r.t = t) (hp : 4 ≤ r.p)
    (htarget : r.p+2 ≤ r.targetOut) (hlocal : r.localityTarget = r.targetOut)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1)
    (hreplicas : r.Fs.length = B) (hcore : coreLength s r.coreWidth r.k = L)
    (v : HS T Q A U) (S : Stacks T A) (hready : plan.Ready r S)
    (hkernel : producer.Ready ([] : List (PackedNormalizedJob A s)) (S.R producer.src) S)
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    ∃ H v' n, ∃ rows : Fin 1 → Fin B → List GaussianInt,
      input.Ready r H ∧ v'.user = v.user ∧
      n ≤ timeCost r+(input.timeCost r H+(producer.timeCost (U := U) [r]+
        20*(descriptorScheduleTape producer.work PackedNormalizedJob.words [r]).length+7)+
        (2*(∑ i, (r.words i).length)+651))+retirementCost r ∧
      (∀ i j, (rows i j).length = L) ∧ (∀ i : Fin 1, r.ExactRowOutput J (List.ofFn (rows i))) ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        (stock r+(input.stock r H+(31*(descriptorScheduleTape producer.work PackedNormalizedJob.words [r]).length+9+
          (C+1)*producer.workspace (U := U) [r])))) depth (plan.run producer) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R producer.result
          ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++S.R producer.result))}) := by
  obtain ⟨v₁,H,n₁,hu₁,hn₁,he₁,hheaders,hI,hO,hL,hframe⟩ := plan.generate_exec (body := body) r v S hready depth
  have hk := hkernel.of_frame (F := H) (by
    intro k hmem
    exact hframe k (hkernelOff k hmem).1 (hkernelOff k hmem).2) (by intro i; rw [hL])
  obtain ⟨v₂,n₂,rows,hu₂,hn₂,hlen,hrows,he₂⟩ := input.run_exec (body := body) producer r
    hsourceReg hworkOff (by intro i heq; exact hresultInput (heq ▸ input.work_mem i)) hcontrolOff
    hA t B L ht hp htarget hlocal J hJ hreplicas hcore v₁ H hheaders hk.hblank hk.hleft hk.hscratch
    (List.eq_nil_of_length_eq_zero (by simpa using hk.hclock)) hk.hsaved hk.hsavedClock C depth hpush hbody
  let output := (List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten
  let G : Stacks T A := {H with R := Function.update H.R producer.result (output++H.R producer.result)}
  have hresultOff (k : Fin T) (hk : k ∈ numericalRegs input) : k ≠ producer.result := by
    intro heq
    apply hresultInput
    rw [←heq]
    rcases List.mem_append.mp hk with hm | hg
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      exact input.masters_mem i
    · have he : k = input.publication.retained 1 := by simpa using hg
      rw [he]
      exact input.retained_mem 1
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) (numericalRegs input) plan.numericalRegs_nodup v₂ G
  have hlength (k : Fin T) (hk : k ∈ numericalRegs input) : (G.R k).length = (H.R k).length := by
    simp only [G,Function.update_of_ne (hresultOff k hk)]
  have hcost : 2*((numericalRegs input).map fun k => (G.R k).length).sum+2*(numericalRegs input).length+1 = retirementCost r := by
    have hmap : ((numericalRegs input).map fun k => (G.R k).length) =
        (List.ofFn r.factoryMasters)++[r.V] := by
      calc
        _ = (numericalRegs input).map (fun k => (H.R k).length) := by
          apply List.map_congr_left
          intro k hk
          exact hlength k hk
        _ = _ := by
          simp only [numericalRegs,List.map_append,List.map_ofFn,Function.comp_def,hheaders.masters,
            List.map_cons,List.map_nil,hheaders.geometryWidth]
    rw [hmap]
    simp only [retirementCost,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,
      numericalRegs,List.length_append,List.length_ofFn,List.length_cons,List.length_nil]
  rw [hcost] at he₃
  have hpref := mn_seq_within_add he₁ he₂
  have hw₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth _ (by
    simpa only [Nat.zero_mul,Nat.add_zero] using hpref.final)
  have hwhole := (ExecWithin.seq hpref hw₃).seq_assoc
  have hblankNumerical (k : Fin T) (hk : k ∈ numericalRegs input) : S.R k = [] := by
    rcases List.mem_append.mp hk with hm | hg
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      exact hready.mastersBlank i
    · have he : k = input.publication.retained 1 := by simpa using hg
      rw [he,←plan.geometryDst]
      exact hready.geometryBlank 115 (by simp)
  have hresultFrame : H.R producer.result = S.R producer.result := hframe _
    (by intro i heq; exact hresultInput (heq ▸ input.masters_mem i))
    (by intro heq; exact hresultInput (heq ▸ input.retained_mem 1))
  have hend : {G with R := fun k => if k ∈ numericalRegs input then [] else G.R k} =
      {S with R := Function.update S.R producer.result (output++S.R producer.result)} := by
    refine Stacks.ext hI hO hL ?_
    funext k
    by_cases hn : k ∈ numericalRegs input
    · simp only [ite_eq_left hn,Function.update_of_ne (hresultOff k hn),hblankNumerical k hn]
    · by_cases hr : k = producer.result
      · subst k; simp [hn,G,hresultFrame]
      · simp only [ite_eq_right hn,G,Function.update_of_ne hr]
        apply hframe
        · intro i heq
          exact hn (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,heq⟩))
        · intro heq
          exact hn (List.mem_append_right _ (by simp [heq]))
  rw [hend] at hwhole
  refine ⟨H,v₃,n₁+(n₂+retirementCost r),rows,hheaders,hu₃.trans (hu₂.trans hu₁),?_,hlen,hrows,?_⟩
  · omega
  · simpa only [run,Nat.add_assoc] using hwhole
end SupplierSetupPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
