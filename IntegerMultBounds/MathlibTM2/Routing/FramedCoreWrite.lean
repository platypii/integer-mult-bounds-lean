module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWrite
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreBank
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreReady

/-! Serialize exactly the nonstream words consumed by the existing framed core
loader. The source bank and scratch restore, and arbitrary output suffixes remain. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {N T Q A : ℕ} {P U : Type}

theorem framedCoreWrite_exec (body : P → Pr P T Q A U) (e : Fin N → Fin T) (str : Fin N)
    (delimiter : Fin (A + 4)) (dst tmp work : Fin T) (hreg : [dst, tmp, work].Nodup)
    (hseparate : ∀ j, j ≠ str → e j ≠ dst ∧ e j ≠ tmp ∧ e j ≠ work)
    (words : Fin N → List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ j, j ≠ str → S.R (e j) = words j)
    (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      configurationWriteCost S.R (framedCoreDestinations e str) ≤
        7 * (delimitedBankFrames delimiter (framedCoreJobs e str words)).length + 1 ∧
      Exec body (delimitedConfigurationWrite delimiter dst tmp work (framedCoreDestinations e str))
        (mk v S) (configurationWriteCost S.R (framedCoreDestinations e str))
        (mk v' { S with R := Function.update S.R dst (delimitedBankFrames delimiter (framedCoreJobs e str words) ++ S.R dst) }) := by
  have hdata : (framedCoreDestinations e str).map (fun j => (j, S.R j)) = framedCoreJobs e str words := by
    unfold framedCoreDestinations framedCoreJobs
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    dsimp only [Function.comp_apply]
    rw [hbank j ((mem_framedCoreRegisters str j).mp hj)]
  obtain ⟨v', hu, he⟩ := delimitedConfigurationWrite_exec body delimiter dst tmp work hreg
    (framedCoreDestinations e str)
    (by intro j hj; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        exact hseparate i ((mem_framedCoreRegisters str i).mp hi)) v S htmp hwork
  rw [hdata] at he
  refine ⟨v', hu, ?_, he⟩
  have hcost := configurationWriteCost_delimited_le delimiter S.R (framedCoreDestinations e str)
  rw [hdata] at hcost
  exact hcost

/-- Serialize a live metadata bank, then clear exactly its nonstream sources.
Only the serialized sources and destination change; the output suffix is retained. -/
theorem framedCoreWriteClean_exec (body : P → Pr P T Q A U)
    (e : Fin N → Fin T) (he : Function.Injective e) (str : Fin N)
    (delimiter : Fin (A + 4)) (dst tmp work : Fin T) (hreg : [dst, tmp, work].Nodup)
    (hseparate : ∀ j, j ≠ str → e j ≠ dst ∧ e j ≠ tmp ∧ e j ≠ work)
    (words : Fin N → List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ j, j ≠ str → S.R (e j) = words j)
    (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ 9 * (delimitedBankFrames delimiter (framedCoreJobs e str words)).length + 2 ∧
      Exec body (.seq (delimitedConfigurationWrite delimiter dst tmp work (framedCoreDestinations e str))
        (metadataClean (framedCoreDestinations e str))) (mk v S) steps
        (mk v' { S with R := Function.update (metadataCleared S.R (framedCoreDestinations e str)) dst (delimitedBankFrames delimiter (framedCoreJobs e str words) ++ S.R dst) }) := by
  let fields := framedCoreDestinations e str
  let frame := delimitedBankFrames delimiter (framedCoreJobs e str words)
  obtain ⟨v₁, hu₁, hc₁, he₁⟩ := framedCoreWrite_exec body e str delimiter dst tmp work hreg hseparate words v S hbank htmp hwork
  let W : Stacks T A := { S with R := Function.update S.R dst (frame ++ S.R dst) }
  obtain ⟨v₂, hu₂, he₂⟩ := metadataClean_exec body fields (framedCoreDestinations_nodup e he str) v₁ W
  have hdst : dst ∉ fields := by
    intro hj
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hj
    exact (hseparate j ((mem_framedCoreRegisters str j).mp hj)).1 heq
  have hcost : metadataCleanCost W.R fields = 2 * frame.length + 1 := by
    rw [show fields = (framedCoreJobs e str words).map Prod.fst from (framedCoreJobs_destinations e str words).symm]
    apply metadataCleanCost_framed
    intro job hj
    change job ∈ (framedCoreRegisters str).map (fun j => (e j, words j)) at hj
    obtain ⟨j, hmem, rfl⟩ := List.mem_map.mp hj
    have hne := (mem_framedCoreRegisters str j).mp hmem
    dsimp only [W]
    rw [Function.update_of_ne (hseparate j hne).1]
    exact hbank j hne
  have hfinal : metadataCleared W.R fields = Function.update (metadataCleared S.R fields) dst (frame ++ S.R dst) :=
    metadataCleared_update S.R fields dst _ hdst
  rw [hcost, hfinal] at he₂
  refine ⟨v₂, configurationWriteCost S.R fields + (2 * frame.length + 1), hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  dsimp only [fields, frame] at hc₁ ⊢
  omega

/-- The serialized-and-cleared prefix bank satisfies the next router's actual
readiness invariant, while its live record stream is untouched. -/
theorem framedCoreWriteClean_ready {M B : ℕ} (str : Fin N) (S : Stacks (N + 3) A)
    (frame : List (Fin (A + 4)))
    (hleft : ∀ j, S.L (framedCoreEmbed N j) = []) (htmp : S.R (framedCoreAux N 1) = [])
    (l : List (List (Fin (A + 4)))) (hl : l.length = M)
    (hshape : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (hstream : S.R (framedCoreEmbed N str) = l.flatten) :
    FramedCoreReady str M B
      { S with R := Function.update (metadataCleared S.R (framedCoreDestinations (framedCoreEmbed N) str)) (framedCoreAux N 0) (frame ++ S.R (framedCoreAux N 0)) } := by
  constructor
  · exact hleft
  · intro j hj
    dsimp only
    rw [Function.update_of_ne (framedCoreEmbed_aux N j 0)]
    apply metadataCleared_at
    exact List.mem_map.mpr ⟨j, (mem_framedCoreRegisters str j).mpr hj, rfl⟩
  · dsimp only
    rw [Function.update_of_ne ((framedCoreAux_injective N).ne (by decide : (1 : Fin 3) ≠ 0)), metadataCleared_keep]
    · exact htmp
    · intro hm
      obtain ⟨j, _, heq⟩ := List.mem_map.mp hm
      exact framedCoreEmbed_aux N j 1 heq
  · refine ⟨l, hl, hshape, ?_⟩
    dsimp only
    rw [Function.update_of_ne (framedCoreEmbed_aux N str 0),
      metadataCleared_keep _ _ _ (framedCoreDestinations_stream _ (framedCoreEmbed_injective N) str)]
    exact hstream

end IntegerMultBounds.MathlibTM2.Routing
