module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadedDyadicScheduleHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedDyadicTranspose
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Compose actual metadata publication and the reusable transpose worker.
The arithmetic bank is disjoint from the worker; only queue and count connect. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace StreamedChunkBank
variable {t₀ T T' Q K : ℕ} {P U : Type}

noncomputable def generatedTransposeCaller (bank : StreamedChunkBank t₀ T Q)
    (g : Fin 117 → Fin T') (e : Fin T → Fin T') : Pr P T' Q (prime+K) U :=
  .seq (embProg g Empty.elim (loadedDyadicScheduleHost (P := Empty)))
    (countedLoop (g 116) (embProg e Empty.elim (bank.program (P := Empty))))

theorem generatedTransposeCaller_exec_within (body : P → Pr P T' Q (prime+K) U)
    (bank : StreamedChunkBank t₀ T Q) (g : Fin 117 → Fin T') (hg : Function.Injective g)
    (e : Fin T → Fin T') (he : Function.Injective e)
    (hbankOff : ∀ j : Fin 117, j.val < 31 → ∀ i, g j ≠ e i)
    (hqueue : g 109 = e bank.queue) (hcountOff : ∀ i, e i ≠ g 116)
    (a b C V : ℕ) (hC : 0 < C) (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V)
    (f : Fin (2^a) → Fin (2^b) → Fin C → Bool)
    (v : HS T' Q (prime+K) U) (S : Stacks T' (prime+K))
    (ha : S.R (g 97) = binSyms V a) (hb : S.R (g 98) = binSyms V b)
    (hseed : S.R (g 102) = binSyms V C) (hz : S.R (g 106) = [])
    (hwidth : (S.R (g 115)).length = V) (hblank : ∀ r, S.R (g (originReg r)) = [])
    (hcount : S.R (g 116) = []) (hready : bank.Ready V (embStk e S))
    (hsrc : (embStk e S).R (bank.ι (reg bank.pay)) = (replicaKeyWords f).map bitSymbol) :
    let rs := (dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => bank.dims)
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (110*V+137+32921*(V+1)^5)+
        (rs.map (fun r => bank.stageTimeCost V (∑ j, ((embStk e S).R (bank.ι j)).length) r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((330*V+411+98763*(V+1)^5)+bank.scheduleStockAllowance V rs)) depth
        (bank.generatedTransposeCaller g e) (Host.mk v S) n (Host.mk v' F)) ∧
      F.R (g 116) = [] ∧
      embStk e F = bank.scheduleState V [] (keyReplicaWords f) (S.R (g 109)) (embStk e S) ∧
      (∀ j : Fin 117, j.val < 31 → F.R (g j) = []) ∧
      (∀ j : Fin 117, 31 ≤ j.val → j ≠ 109 → j ≠ 116 → (∀ i, e i ≠ g j) →
        F.R (g j) = S.R (g j)) ∧
      ∀ outside, (∀ j, g j ≠ outside) → (∀ i, e i ≠ outside) →
        F.L outside = S.L outside ∧ F.R outside = S.R outside := by
  classical
  let Sg := embStk g S
  obtain ⟨vg,mg,hug,hmg,heg⟩ := loadedDyadicScheduleHost_exec
    (body := fun z : Empty => nomatch z) a b C V hbits hfit
    (by
      have h2 := Networks.le_coefficientExponent
        ((by decide : 2 ≤ 53000).trans (Nat.lt_two_pow_self.le))
      have hh := Networks.two_pow_le_coefficientBound h2
      have hp := Networks.Shared50ModularControl.coefficientBound_lt_prime
      norm_num only [Nat.reducePow] at hh
      omega) (embDn g v) Sg ha hb hseed hz hwidth hblank
  have htime := hmg
  obtain ⟨vm,M,hegen,hdn,hum,hM,hMoff⟩ := exec_emb (e := g) (ι := (Empty.elim : Empty → P)) (body' := body) hg (fun z : Empty => nomatch z) heg v rfl S rfl
  have hgenL : ∀ i, M.L i = S.L i := by
    intro i
    by_cases hi : ∃ j, g j = i
    · obtain ⟨j,rfl⟩ := hi
      exact congrArg (fun z => z.L j) hM
    · exact (hMoff i (by simpa using hi)).1
  have hgenR : ∀ i, i ≠ bank.queue → M.R (e i) = S.R (e i) := by
    intro i hi
    by_cases hj : ∃ j, g j = e i
    · obtain ⟨j,hj⟩ := hj
      have hj31 : ¬j.val < 31 := fun h => hbankOff j h i hj
      have hj109 : j ≠ 109 := by
        intro h; subst j
        exact hi (he (hj.symm.trans hqueue))
      have hj116 : j ≠ 116 := by
        intro h; subst j
        exact hcountOff i hj.symm
      have hh := congrArg (fun z => z.R j) hM
      simpa only [Sg,embStk_R,hj,hj31,ite_false,hj109,hj116] using hh
    · exact (hMoff (e i) (by simpa using hj)).2
  have hreadyM : bank.Ready V (embStk e M) :=
    Ready.of_frame bank V (embStk e S) (embStk e M) hready
      (fun i => (hgenL (e i)).trans (hready.hL i)) (fun i hi _ => hgenR i hi)
  have hcountM : (M.R (g 116)).length = dyadicStageCount (a+b) a b := by
    have hh := congrArg (fun z => z.R 116) hM
    simpa [Sg,embStk,hcount] using congrArg List.length hh
  have hqueueM : (embStk e M).R bank.queue =
      (dyadicScheduleValues (a+b) a b C).flatMap (binSyms V)++S.R (g 109) := by
    have hh := congrArg (fun z => z.R 109) hM
    simpa [Sg,embStk,hqueue] using hh
  have hsrcM : (embStk e M).R (bank.ι (reg bank.pay)) = (replicaKeyWords f).map bitSymbol := by
    rw [embStk_R,hgenR _ (bank.hqueueOff _).symm]
    exact hsrc
  obtain ⟨vf,F,mw,huf,hmw,hw,hcounter,hF,hFoff⟩ := bank.generatedDyadicTranspose_exec_within
    body e he (g 116) hcountOff hC V hbits hfit f (S.R (g 109)) vm M hreadyM hcountM hqueueM hsrcM
  have hstock : (∑ j, ((embStk e M).R (bank.ι j)).length) =
      ∑ j, ((embStk e S).R (bank.ι j)).length := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [embStk_R,hgenR _ (bank.hqueueOff _).symm]
  rw [hstock] at hmw
  refine ⟨vf,F,mg+mw,huf.trans (hum.trans hug),by omega,?_,hcounter,?_,?_,?_,?_⟩
  · intro depth
    have htg := mn_native_exec_within hegen 3
      (embProg_native g Empty.elim _ loadedDyadicScheduleHost_native)
      depth (mnSize (Host.mk v S)+depth+(330*V+411+98763*(V+1)^5)) (by nlinarith only [htime])
    exact mn_seq_within_add htg (hw depth)
  · rw [hF]
    apply Stacks.ext
    · exact congrArg (fun z => z.inp) hM
    · exact congrArg (fun z => z.out) hM
    · rfl
    · funext i
      by_cases hp : i = bank.ι (reg bank.pay)
      · subst i; simp [scheduleState]
      · by_cases hq : i = bank.queue
        · subst i; simp [scheduleState,Function.update_of_ne hp]
        · simp only [scheduleState,Function.update_of_ne hp,Function.update_of_ne hq]
          exact hgenR i hq
  · intro j hj
    have hgj : g j ≠ g 116 := fun h => by have := hg h; subst j; norm_num at hj
    rw [(hFoff (g j) hgj (fun i => (hbankOff j hj i).symm)).2]
    have hh := congrArg (fun z => z.R j) hM
    simpa only [embStk_R,ite_eq_left hj] using hh
  · intro j hj hj109 hj116 hoff
    have hc : g j ≠ g 116 := fun h => hj116 (hg h)
    rw [(hFoff (g j) hc hoff).2]
    have hh := congrArg (fun z => z.R j) hM
    have hj31 : ¬j.val < 31 := by omega
    simpa only [Sg,embStk_R,hj31,ite_false,hj109,hj116] using hh
  · intro outside hgOff heOff
    have hc : outside ≠ g 116 := (hgOff 116).symm
    exact ⟨((hFoff outside hc heOff).1).trans (hMoff outside hgOff).1,
      ((hFoff outside hc heOff).2).trans (hMoff outside hgOff).2⟩

end StreamedChunkBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
