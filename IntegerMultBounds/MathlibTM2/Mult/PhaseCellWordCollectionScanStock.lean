module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWordCollectionScan
public import IntegerMultBounds.MathlibTM2.Node.ScanPStock

/-! Word collection shares one native iteration reserve above final output stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem wordCollectionScan_exec_within (step : Pr P T Q A U) (count saved dst cursor : Fin T)
    (hregs : [count,saved,dst,cursor].Nodup) (w L : ℕ) (F : ℕ → GaussianInt) (cost : ℕ → ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hcount : (S.R count).length = L) (hsaved : S.R saved = [])
    (cap c depth : ℕ) (hc : 1 ≤ c) (hnative : mnNativePushBound c step)
    (hcost : ∀ j < L, cost j ≤ cap)
    (hstep : ∀ j < L, ∀ (vi : HS T Q A U) (Si : Stacks T A),
      (∀ k, k ≠ count → k ≠ saved → Si.R k = wordCollectionR S.R dst cursor w F j k) →
      ∃ vf m, vf.user = vi.user ∧ m ≤ cost j ∧ Exec body step (mk vi Si) m
        (mk vf {Si with R := (Function.update (Function.update Si.R dst (csyms A w (F j)++Si.R dst))
          cursor (tick::Si.R cursor))})) :
    ∃ v' m, v'.user = v.user ∧ m ≤ (∑ j ∈ Finset.range L, (cost j+3))+2*L+4 ∧
      ExecWithin body
        (fun d z => mnSize z+d ≤
          mnSize (mk v' {S with R := wordCollectionR S.R dst cursor w F L})+depth+c*(cap+2))
        depth (scanP count saved step) (mk v S) m
        (mk v' {S with R := wordCollectionR S.R dst cursor w F L}) := by
  have hr := hregs
  regs_ne hr
  let Ψ := wordCollectionR S.R dst cursor w F
  have hiter : IterStockSpec body step count saved Ψ cap L := by
    intro j hj vi Si hSi
    obtain ⟨vf,m,huser,hm,hex⟩ := hstep j hj vi Si hSi
    let R' := Function.update (Function.update Si.R dst (csyms A w (F j)++Si.R dst)) cursor (tick::Si.R cursor)
    refine ⟨vf,R',m,huser,(hm.trans (hcost j hj)),hex,by simp [R',‹count ≠ dst›,‹count ≠ cursor›],
      by simp [R',‹saved ≠ dst›,‹saved ≠ cursor›],?_,?_⟩
    · intro k hkCount hkSaved
      by_cases hkDst : k = dst
      · subst k
        rw [show R' dst = csyms A w (F j)++Si.R dst by simp [R',‹dst ≠ cursor›],hSi dst ‹dst ≠ count› ‹dst ≠ saved›]
        simp [Ψ,wordCollectionR,List.range_succ,List.reverse_append,cstream,List.append_assoc,‹dst ≠ cursor›]
      by_cases hkCursor : k = cursor
      · subst k
        rw [show R' cursor = tick::Si.R cursor by simp [R'],hSi cursor ‹cursor ≠ count› ‹cursor ≠ saved›]
        simp [Ψ,wordCollectionR,List.replicate_succ]
      rw [show R' k = Si.R k by simp [R',hkDst,hkCursor],hSi k hkCount hkSaved]
      simp [Ψ,wordCollectionR,hkDst,hkCursor]
    · let D : Stacks T A := {Si with R := Function.update Si.R dst (csyms A w (F j)++Si.R dst)}
      have hd := mn_size_update (mk vi Si) vi (.rt dst) (csyms A w (F j)++Si.R dst)
      have ht : mnSize (mk vf {D with R := Function.update D.R cursor (tick::Si.R cursor)})+
          (D.R cursor).length = mnSize (mk vi D)+(tick::Si.R cursor).length := by
        simpa only [mk,update_rt,get_rt] using
          mn_size_update (mk vi D) vf (.rt cursor) (tick::Si.R cursor)
      have hcursor : D.R cursor = Si.R cursor := by simp [D,Ne.symm ‹dst ≠ cursor›]
      simp only [mk,update_rt,get_rt,List.length_append] at hd
      rw [hcursor,List.length_cons] at ht
      change mnSize (mk vi Si) ≤ mnSize (mk vf {D with R := Function.update D.R cursor (tick::Si.R cursor)})
      change mnSize (mk vi D)+(Si.R dst).length = mnSize (mk vi Si)+_ at hd
      omega
  obtain ⟨v',m,hu,hm,he⟩ := wordCollectionScan_exec step count saved dst cursor hregs w L F cost
    v S hcount hsaved hstep
  refine ⟨v',m,hu,hm,?_⟩
  apply scanP_within_final_stock ‹count ≠ saved› hc hnative hiter 0 v S
    (by omega) ?_ he depth
  intro k _ _
  by_cases hd : k = dst <;> by_cases hc : k = cursor <;> simp [Ψ,wordCollectionR,hd,hc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
