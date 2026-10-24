module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Install compact binary stride/residue inputs into a reusable compiler bank,
execute a framed call, then erase both installed words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingControlJobs (rg : Fin 7 → Fin T) : List (MetadataJob T) :=
  [.copy (rg 0) (rg 2) false, .copy (rg 1) (rg 3) false]

def matchingControlBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 7 → Fin T)
    (L K r : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update R (rg 3) (binSyms L r)) (rg 2) (binSyms L K)

def matchingControlScope (rg : Fin 7 → Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (metadataInstall (rg 4) (rg 5) (rg 6) (matchingControlJobs rg))
    (.seq call (metadataClean [rg 2, rg 3]))

theorem matchingControlScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 7 → Fin T) (hrg : Function.Injective rg) (L K r : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hstride : S.R (rg 0) = binSyms L K) (hresidue : S.R (rg 1) = binSyms L r)
    (hblank : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → S.R (rg j) = [])
    (str : Fin T) (hstr : str ≠ rg 2 ∧ str ≠ rg 3) (output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := matchingControlBank S.R rg L K r }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R str output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ price + 16 * L + 20 ∧
      Exec body (matchingControlScope rg call) (mk v S) m
        (mk v' { S with R := Function.update S.R str output }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := metadataInstall_exec body (matchingControlJobs rg)
    (rg 4) (rg 5) (rg 6)
    (by simp [matchingControlJobs, MetadataJob.dst, hrg.eq_iff])
    (by intro job hj; simp only [matchingControlJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> simp [MetadataJob.src, MetadataJob.dst, List.nodup_cons, hrg.eq_iff])
    (by intro job hj other ho; simp only [matchingControlJobs, List.mem_cons, List.not_mem_nil, or_false] at hj ho
        rcases hj with rfl | rfl <;> rcases ho with rfl | rfl <;> simp [MetadataJob.src, MetadataJob.dst, hrg.eq_iff]) v S
    (by intro job hj; simp only [matchingControlJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> trivial)
    (by intro job hj; simp only [matchingControlJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> apply hblank <;> decide)
    (hblank 4 (by decide) (by decide)) (hblank 5 (by decide) (by decide)) (hblank 6 (by decide) (by decide))
  have hinstalled : metadataInstalled S.R (matchingControlJobs rg) = matchingControlBank S.R rg L K r := by
    simp [matchingControlJobs, metadataInstalled, MetadataJob.contents, MetadataJob.dst,
      matchingControlBank, hstride, hresidue]
  have hinstallCost : metadataInstallCost S.R (matchingControlJobs rg) = 12 * L + 15 := by
    simp [matchingControlJobs, metadataInstallCost, MetadataJob.cost, hstride, hresidue, length_binSyms]
    ring
  rw [hinstalled] at he₁
  rw [hinstallCost] at hm₁
  let C : Stacks T A := { S with R := matchingControlBank S.R rg L K r }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R str output }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body [rg 2, rg 3] (by simp [hrg.eq_iff]) v₂ D
  have hcost : metadataCleanCost D.R [rg 2, rg 3] = 4 * L + 5 := by
    simp [metadataCleanCost, D, C, matchingControlBank, hstr.1.symm, hstr.2.symm, hrg.eq_iff, length_binSyms]
    ring
  have hrestored : metadataCleared C.R [rg 2, rg 3] = S.R := by
    rw [show C.R = metadataInstalled S.R (matchingControlJobs rg) from hinstalled.symm]
    exact metadataClean_restore S.R (matchingControlJobs rg) (by
      intro job hj; simp only [matchingControlJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> apply hblank <;> decide)
  have hfinal : metadataCleared D.R [rg 2, rg 3] = Function.update S.R str output := by
    rw [show D.R = Function.update C.R str output from rfl,
      metadataCleared_update _ _ _ _ (by simp [hstr.1, hstr.2]), hrestored]
  rw [hcost, hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + (4 * L + 5)), hu₃.trans (hu₂.trans hu₁), by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
