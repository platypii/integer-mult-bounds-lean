module

public import IntegerMultBounds.MathlibTM2.Node.Params
import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! A structural row scan shares its fixed transducer, restores the source from
one reverse archive, and records the actual reverse replica publication order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {P U K : Type} {body : P → Pr P T Q A U}

def restoringRowScan (replicas saved source archive : Fin T) (step : Pr P T Q A U) : Pr P T Q A U :=
  .seq (scanP replicas saved step) (moveR archive source id)

theorem restoringRowScan_exec (replicas saved source archive dst : Fin T)
    (hreg : [replicas,saved,source,archive,dst].Nodup)
    (step : Pr P T Q A U) (cost : ℕ) (xs : List K)
    (row payload : K → List (Fin (A+4))) (borrowed : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsource : S.R source = xs.flatMap row++borrowed) (harchive : S.R archive = [])
    (hreplicas : (S.R replicas).length = xs.length) (hsaved : S.R saved = [])
    (hstep : ∀ x ∈ xs, ∀ (v₀ : HS T Q A U) (F : Stacks T A) (tail : List (Fin (A+4))),
      (∀ k, k ∉ [replicas,saved,source,archive,dst] → F.R k = S.R k) →
      F.R source = row x++tail →
      ∃ v' n, v'.user = v₀.user ∧ n ≤ cost ∧ Exec body step (mk v₀ F) n
        (mk v' {F with R := (Function.update (Function.update (Function.update F.R source tail)
          archive ((row x).reverse++F.R archive)) dst (payload x++F.R dst))})) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ xs.length*(cost+5)+4+2*(xs.flatMap row).length+2 ∧
      Exec body (restoringRowScan replicas saved source archive step) (mk v S) n
        (mk v' {S with R := Function.update S.R dst (xs.reverse.flatMap payload++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  let Ψ := fun j => Function.update (Function.update (Function.update S.R source
    ((xs.drop j).flatMap row++borrowed)) archive ((xs.take j).flatMap row).reverse)
      dst ((xs.take j).reverse.flatMap payload++S.R dst)
  have hi : IterSpec body step replicas saved Ψ (fun _ => cost) xs.length := by
    intro j hj v₀ F hF
    have hbase (k : Fin T) (hkSource : k ≠ source) (hkArchive : k ≠ archive) (hkDst : k ≠ dst)
        (hkRep : k ≠ replicas) (hkSaved : k ≠ saved) : F.R k = S.R k := by
      rw [hF k hkRep hkSaved]
      simp [Ψ,hkSource,hkArchive,hkDst]
    have hs : F.R source = row xs[j]++((xs.drop (j+1)).flatMap row++borrowed) := by
      rw [hF source (Ne.symm ‹replicas ≠ source›) (Ne.symm ‹saved ≠ source›)]
      simp only [Ψ,Function.update_of_ne ‹source ≠ dst›,Function.update_of_ne ‹source ≠ archive›,
        Function.update_self]
      rw [List.drop_eq_getElem_cons hj,List.flatMap_cons,List.append_assoc]
    have ha : F.R archive = ((xs.take j).flatMap row).reverse := by
      rw [hF archive (Ne.symm ‹replicas ≠ archive›) (Ne.symm ‹saved ≠ archive›)]
      simp [Ψ,‹archive ≠ dst›]
    have hd : F.R dst = (xs.take j).reverse.flatMap payload++S.R dst := by
      rw [hF dst (Ne.symm ‹replicas ≠ dst›) (Ne.symm ‹saved ≠ dst›)]
      simp [Ψ]
    obtain ⟨v₁,n,hu,hn,he⟩ := hstep xs[j] (List.getElem_mem hj) v₀ F
      ((xs.drop (j+1)).flatMap row++borrowed) (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
        exact hbase k hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2 hk.1 hk.2.1) hs
    let R := Function.update (Function.update (Function.update F.R source
      ((xs.drop (j+1)).flatMap row++borrowed)) archive ((row xs[j]).reverse++F.R archive))
        dst (payload xs[j]++F.R dst)
    refine ⟨v₁,R,n,hu,hn,he,?_,?_,?_⟩
    · simp [R,‹replicas ≠ dst›,‹replicas ≠ archive›,‹replicas ≠ source›]
    · simp [R,‹saved ≠ dst›,‹saved ≠ archive›,‹saved ≠ source›]
    · intro k hkRep hkSaved
      by_cases hkDst : k = dst
      · subst k
        simp only [R,Ψ,Function.update_self]
        rw [hd,List.take_succ_eq_append_getElem hj]
        simp only [List.reverse_append,List.reverse_singleton,List.flatMap_append,List.flatMap_cons,
          List.flatMap_nil,List.append_nil,List.append_assoc]
      by_cases hkArchive : k = archive
      · subst k
        simp only [R,Ψ,Function.update_of_ne ‹archive ≠ dst›,Function.update_self]
        rw [ha,List.take_succ_eq_append_getElem hj]
        simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.reverse_append]
      by_cases hkSource : k = source
      · subst k
        simp [R,Ψ,‹source ≠ dst›,‹source ≠ archive›]
      simp only [R,Ψ,Function.update_of_ne hkDst,Function.update_of_ne hkArchive,Function.update_of_ne hkSource]
      exact hbase k hkSource hkArchive hkDst hkRep hkSaved
  have hzero : Ψ 0 = S.R := by
    simp only [Ψ,List.take_zero,List.drop_zero,List.flatMap_nil,List.reverse_nil,List.nil_append]
    rw [←hsource,←harchive]
    simp only [Function.update_eq_self]
  obtain ⟨v₁,R,n,hu,hn,he,hrep,hsrep,hR⟩ := scanP_exec (body := body) ‹replicas ≠ saved› hi 0 v S
    (by simpa only [hreplicas,Nat.zero_add] using Nat.le_refl xs.length) (by intro k _ _; rw [hzero])
  let F : Stacks T A := {S with R := R}
  have ha : F.R archive = (xs.flatMap row).reverse := by
    rw [show F.R archive = R archive from rfl,hR archive (Ne.symm ‹replicas ≠ archive›) (Ne.symm ‹saved ≠ archive›)]
    simp [Ψ,hreplicas,‹archive ≠ dst›]
  have hs : F.R source = borrowed := by
    rw [show F.R source = R source from rfl,hR source (Ne.symm ‹replicas ≠ source›) (Ne.symm ‹saved ≠ source›)]
    simp [Ψ,hreplicas,‹source ≠ dst›,‹source ≠ archive›]
  have hd : F.R dst = xs.reverse.flatMap payload++S.R dst := by
    rw [show F.R dst = R dst from rfl,hR dst (Ne.symm ‹replicas ≠ dst›) (Ne.symm ‹saved ≠ dst›)]
    simp [Ψ,hreplicas]
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body archive source (Ne.symm ‹source ≠ archive›) id v₁ F
  refine ⟨v₂,n+(2*(xs.flatMap row).length+2),hu₂.trans hu,?_,(Exec.seq he he₂).cast ?_ ?_⟩
  · simp only [hreplicas,hsaved,List.length_nil,Finset.sum_const,Finset.card_range,smul_eq_mul] at hn
    nlinarith only [hn]
  · rw [ha,List.length_reverse]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hkSource : k = source
    · subst k
      simp only [movedR,Function.update_self,List.map_id,ha,List.reverse_reverse,
        Function.update_of_ne ‹source ≠ dst›]
      rw [hs]
      exact hsource.symm
    by_cases hkArchive : k = archive
    · subst k
      simp [movedR,‹archive ≠ dst›,Ne.symm ‹source ≠ archive›,harchive]
    by_cases hkDst : k = dst
    · subst k
      simpa only [movedR,Function.update_of_ne (Ne.symm ‹source ≠ dst›),
        Function.update_of_ne (Ne.symm ‹archive ≠ dst›),Function.update_self] using hd
    by_cases hkRep : k = replicas
    · subst k
      simp [F,movedR,‹replicas ≠ source›,‹replicas ≠ archive›,‹replicas ≠ dst›,hrep,hsaved]
    by_cases hkSaved : k = saved
    · subst k
      simp [F,movedR,‹saved ≠ source›,‹saved ≠ archive›,‹saved ≠ dst›,hsrep,hsaved]
    simp only [movedR,Function.update_of_ne hkSource,Function.update_of_ne hkArchive,Function.update_of_ne hkDst]
    change R k = S.R k
    rw [hR k hkRep hkSaved]
    simp [Ψ,hreplicas,hkSource,hkArchive,hkDst]

end IntegerMultBounds.MathlibTM2.Host
