module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeBatch
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! A compiler borrows an installed bank of resized operands and then erases
that bank. Structural installation and cleanup both have explicit prices. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U J : Type}

theorem binaryResizeBatchBank_at (R : Fin T → List (Fin (A + 4))) (rg : J → Fin 9 → Fin T)
    (W x : J → ℕ) (jobs : List J) (hdst : (jobs.map (fun j => rg j 3)).Nodup)
    (j : J) (hj : j ∈ jobs) : binaryResizeBatchBank R rg W x jobs (rg j 3) = binSyms (W j) (x j) := by
  induction jobs with
  | nil => simp at hj
  | cons k jobs ih =>
      have hn := List.nodup_cons.mp hdst
      rcases List.mem_cons.mp hj with rfl | hj
      · simp [binaryResizeBatchBank]
      · have hne : rg j 3 ≠ rg k 3 := by
          intro he
          exact hn.1 (List.mem_map.mpr ⟨j, hj, he⟩)
        rw [binaryResizeBatchBank, Function.update_of_ne hne]
        exact ih hn.2 hj

theorem binaryResizeBatchBank_clean (R : Fin T → List (Fin (A + 4))) (rg : J → Fin 9 → Fin T)
    (W x : J → ℕ) (jobs : List J) (hblank : ∀ j ∈ jobs, R (rg j 3) = []) :
    metadataCleared (binaryResizeBatchBank R rg W x jobs) (jobs.map (fun j => rg j 3)) = R := by
  funext k
  by_cases hk : k ∈ jobs.map (fun j => rg j 3)
  · rw [metadataCleared_at _ _ _ hk]
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    exact (hblank j hj).symm
  · rw [metadataCleared_keep _ _ _ hk, binaryResizeBatchBank_keep R rg W x jobs k hk]

theorem binaryResizeBatchBank_cleanCost_le (R : Fin T → List (Fin (A + 4))) (rg : J → Fin 9 → Fin T)
    (W x : J → ℕ) (jobs : List J) (hdst : (jobs.map (fun j => rg j 3)).Nodup)
    (B : ℕ) (hB : ∀ j ∈ jobs, W j ≤ B) :
    metadataCleanCost (binaryResizeBatchBank R rg W x jobs) (jobs.map (fun j => rg j 3)) ≤
      jobs.length * (2 * B + 2) + 1 := by
  have hc := metadataCleanCost_le (binaryResizeBatchBank R rg W x jobs) (jobs.map (fun j => rg j 3)) B (by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    rw [binaryResizeBatchBank_at R rg W x jobs hdst j hj, length_binSyms]
    exact hB j hj)
  simpa only [List.length_map] using hc

def binaryResizeBatchScope (rg : J → Fin 9 → Fin T) (jobs : List J) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (binaryResizeBatchProgram rg jobs) (.seq call (metadataClean (jobs.map (fun j => rg j 3))))

theorem binaryResizeBatchScope_exec (body : P → Pr P T Q A U)
    (rg : J → Fin 9 → Fin T) (hrg : ∀ j, Function.Injective (rg j))
    (M L W x : J → ℕ) (hW : ∀ j, W j < 2 ^ M j) (hx : ∀ j, x j < 2 ^ L j)
    (jobs : List J) (hdst : (jobs.map (fun j => rg j 3)).Nodup)
    (hseparate : ∀ j i, i ≠ 3 → ∀ k, rg j i ≠ rg k 3)
    (B : ℕ) (hB : ∀ j ∈ jobs, W j ≤ B)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : ∀ j, S.R (rg j 0) = binSyms (M j) (W j))
    (hvalue : ∀ j, S.R (rg j 1) = binSyms (L j) (x j))
    (houtput : ∀ j ∈ jobs, S.R (rg j 3) = [])
    (hblank : ∀ j i, i ≠ 0 → i ≠ 1 → i ≠ 3 → S.R (rg j i) = [])
    (str : Fin T) (hstr : str ∉ jobs.map (fun j => rg j 3)) (output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := binaryResizeBatchBank S.R rg W x jobs }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R str output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ binaryResizeBatchCost M L W jobs + price + (jobs.length * (2 * B + 2) + 1) ∧
      Exec body (binaryResizeBatchScope rg jobs call) (mk v S) m
        (mk v' { S with R := Function.update S.R str output }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryResizeBatch_exec body rg hrg M L W x hW hx jobs hdst hseparate
    v S hwidth hvalue houtput hblank
  let C : Stacks T A := { S with R := binaryResizeBatchBank S.R rg W x jobs }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R str output }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body _ hdst v₂ D
  have hcost : metadataCleanCost D.R (jobs.map (fun j => rg j 3)) ≤ jobs.length * (2 * B + 2) + 1 := by
    rw [metadataCleanCost_congr _ (R' := C.R) (by
      intro k hk
      apply Function.update_of_ne
      intro he
      exact hstr (he ▸ hk))]
    exact binaryResizeBatchBank_cleanCost_le S.R rg W x jobs hdst B hB
  have hfinal : metadataCleared D.R (jobs.map (fun j => rg j 3)) = Function.update S.R str output := by
    rw [show D.R = Function.update C.R str output from rfl, metadataCleared_update _ _ _ _ hstr]
    rw [binaryResizeBatchBank_clean S.R rg W x jobs houtput]
  rw [hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + metadataCleanCost D.R (jobs.map (fun j => rg j 3))), hu₃.trans (hu₂.trans hu₁),
    by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
