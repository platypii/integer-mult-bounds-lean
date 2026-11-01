module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedNormalizedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedRecoveryPublication

/-! Complete computed local recovery followed by physical ordered publication. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace ComputedRecoveryPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def orderedFinal (plan : ComputedRecoveryPlan T) (normalize : RecoveryNormalizePlan T)
    (e : Fin 14 → Fin T) (S : Stacks T A) (word : List (Fin (A+4))) : Stacks T A :=
  {S with R := (Function.update (Function.update
    (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) normalize.src (S.R normalize.src))
    (e 7) (word++S.R (e 7)))}

theorem ordered_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (hreg : link.reg = crop.reg)
    (hsupportMaster : ∀ k, normalize.support queue k → ∀ i, plan.master.masters i ≠ k)
    (hsupportPayload : ∀ k, normalize.support queue k → k ≠ plan.work 124)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (r : PackedNormalizedJob A s) (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore)
    (v : HS T Q A U) (S : Stacks T A)
    (hready : normalize.UnaryReady queue r r.Fs.length wl S)
    (hp : (S.R plan.precision).length = r.p) (hW : (S.R plan.packet).length = r.W)
    (hN : (S.R plan.replicas).length = r.Fs.length)
    (hvalues : ∀ i, (S.R (plan.master.parameters i)).length = r.masterInput.values i)
    (hwidth : S.R (plan.master.scalar .wr) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.master.scalar i) = [])
    (hmasters : ∀ i, S.R (plan.master.masters i) = [])
    (hmasterScratch : ∀ k ∈ [plan.master.word,plan.master.saved,plan.master.tmp,plan.master.queue], S.R k = [])
    (hblank : ∀ i, i ≠ 124 → S.R (plan.work i) = []) (hleft : ∀ i, S.L (plan.work i) = [])
    (hpayload : S.R (plan.work 124) = cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten)
    (hscratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = [])
    (hclock : S.R plan.clock = []) (hsaved : S.R plan.saved = []) (hsavedClock : S.R plan.savedClock = [])
    (hoffset : (S.R (crop.reg 3)).length = r.radius)
    (hrows : (S.R (crop.reg 4)).length = coreLength s r.coreWidth r.k)
    (e : Fin 14 → Fin T) (he : Function.Injective e)
    (hsource : e 6 = normalize.src)
    (houtside : ∀ k ∈ ([(0 : Fin 14),1,2,7]), e k ∉ List.ofFn plan.work)
    (horderRows : (S.R (e 0)).length = coreLength s r.coreWidth r.k)
    (horderWidth : (S.R (e 1)).length = r.W)
    (horderReplicas : (S.R (e 2)).length = r.Fs.length)
    (horderBlank : ∀ k ∈ ([(3 : Fin 14),4,5,8,9,10,11,12,13]),
      e k ∈ List.ofFn plan.work ∨ S.R (e k) = []) :
    ∃ word v' n, r.output word ∧ v'.user = v.user ∧
      n ≤ plan.normalizedTimeCost b r+restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W ∧
      Exec body (.seq (plan.normalizedProgram b normalize queue link)
        (embProg e Empty.elim restoreReplicaOrder)) (Host.mk v S) n
        (Host.mk v' (orderedFinal plan normalize e S word)) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (plan.normalizedStock b r Cprog+2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))
          depth (.seq (plan.normalizedProgram b normalize queue link) (embProg e Empty.elim restoreReplicaOrder))
          (Host.mk v S) n (Host.mk v' (orderedFinal plan normalize e S word)) := by
  obtain ⟨Ds,hlen,v₁,n₁,hu₁,hn₁,hex₁,hgood,htrace₁⟩ := plan.normalized_exec (body := body) b normalize queue crop link hreg
    hsupportMaster hsupportPayload hreplicaCount hreplicaSpare r wl hwl v S hready hp hW hN hvalues
    hwidth hscalar hmasters hmasterScratch hblank hleft hpayload hscratch hclock hsaved hsavedClock hoffset hrows
  let M : Stacks T A := {S with R := (Function.update
    (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) normalize.src
    ((Ds.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++S.R normalize.src))}
  have hne (k : Fin 14) (hk : k ≠ 6) : e k ≠ normalize.src := by
    rw [←hsource]; exact fun h => hk (he h)
  have hstable (k : Fin 14) (hk : k ∈ ([(0 : Fin 14),1,2,7])) : M.R (e k) = S.R (e k) := by
    have hk6 : k ≠ 6 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
    simp only [M,Function.update_of_ne (hne k hk6),ite_eq_right (houtside k hk)]
  have hblankM : ∀ k ∈ ([(3 : Fin 14),4,5,8,9,10,11,12,13]), M.R (e k) = [] := by
    intro k hk
    have hk6 : k ≠ 6 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [M,Function.update_of_ne (hne k hk6)]
    rcases horderBlank k hk with hw | hb
    · exact ite_eq_left hw
    · split <;> first | rfl | exact hb
  obtain ⟨v₂,n₂,hu₂,hn₂,hex₂,houtput,htrace₂⟩ := r.restoreReplicaOrder_exec (body := body) e he Ds
    (S.R normalize.src) v₁ M
    (by rw [hstable 0 (by simp)]; exact horderRows)
    (by rw [hstable 1 (by simp)]; exact horderWidth)
    (by rw [hstable 2 (by simp),hlen]; exact horderReplicas)
    hblankM (by simp only [M,hsource,Function.update_self]) hgood
  let word := (Ds.reverse.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten
  have hfinal : {M with R := (Function.update (Function.update M.R (e 6) (S.R normalize.src)) (e 7)
      (word++M.R (e 7)))} = orderedFinal plan normalize e S word := by
    have hd := hstable 7 (by simp)
    rw [hd]
    simp only [M,orderedFinal,hsource,Function.update_idem]
  change Exec body _ (Host.mk v₁ M) n₂ _ at hex₂
  rw [hfinal] at hex₂
  refine ⟨word,v₂,n₁+n₂,houtput,hu₂.trans hu₁,?_,Exec.seq hex₁ hex₂,?_⟩
  · rw [hlen] at hn₂; exact Nat.add_le_add hn₁ hn₂
  · intro Cprog hpush hbody depth
    have ht₁ := htrace₁ Cprog hpush hbody 0
    have ht₂ := htrace₂ 0
    rw [hfinal,hlen] at ht₂
    have ht := mn_seq_within_add ht₁ ht₂
    simpa only [Nat.zero_add] using ht.shift depth (J := fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
      (plan.normalizedStock b r Cprog+2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))
      (by intro d z hz; omega)

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
