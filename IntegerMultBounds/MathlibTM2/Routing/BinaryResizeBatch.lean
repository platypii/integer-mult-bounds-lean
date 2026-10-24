module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeCopy

/-! Install a fixed bank of resized binary operands. Numeric dimensions appear
only in the proof ledger; executed code depends on register maps and job order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U J : Type}

def binaryResizeBatchProgram (rg : J → Fin 9 → Fin T) : List J → Pr P T Q A U
  | [] => .act .done
  | j :: jobs => .seq (binaryResizeBatchProgram rg jobs) (binaryResizeCopyProgram (rg j))

def binaryResizeBatchBank (R : Fin T → List (Fin (A + 4))) (rg : J → Fin 9 → Fin T)
    (W x : J → ℕ) : List J → Fin T → List (Fin (A + 4))
  | [] => R
  | j :: jobs => Function.update (binaryResizeBatchBank R rg W x jobs) (rg j 3) (binSyms (W j) (x j))

def binaryResizeBatchCost (M L W : J → ℕ) : List J → ℕ
  | [] => 1
  | j :: jobs => binaryResizeBatchCost M L W jobs +
      (2 * M j * (4 * W j + 11) + 12 * L j + 26 * W j + 42)

theorem binaryResizeBatchBank_keep (R : Fin T → List (Fin (A + 4))) (rg : J → Fin 9 → Fin T)
    (W x : J → ℕ) (jobs : List J) (k : Fin T) (hk : k ∉ jobs.map (fun j => rg j 3)) :
    binaryResizeBatchBank R rg W x jobs k = R k := by
  induction jobs with
  | nil => rfl
  | cons j jobs ih =>
      rw [binaryResizeBatchBank, Function.update_of_ne (by intro he; exact hk (by simp [he]))]
      exact ih (fun hm => hk (by simp [hm]))

theorem binaryResizeBatch_exec (body : P → Pr P T Q A U)
    (rg : J → Fin 9 → Fin T) (hrg : ∀ j, Function.Injective (rg j))
    (M L W x : J → ℕ) (hW : ∀ j, W j < 2 ^ M j) (hx : ∀ j, x j < 2 ^ L j)
    (jobs : List J) (hdst : (jobs.map (fun j => rg j 3)).Nodup)
    (hseparate : ∀ j i, i ≠ 3 → ∀ k, rg j i ≠ rg k 3)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : ∀ j, S.R (rg j 0) = binSyms (M j) (W j))
    (hvalue : ∀ j, S.R (rg j 1) = binSyms (L j) (x j))
    (houtput : ∀ j ∈ jobs, S.R (rg j 3) = [])
    (hblank : ∀ j i, i ≠ 0 → i ≠ 1 → i ≠ 3 → S.R (rg j i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ binaryResizeBatchCost M L W jobs ∧
      Exec body (binaryResizeBatchProgram rg jobs) (mk v S) m
        (mk v' { S with R := binaryResizeBatchBank S.R rg W x jobs }) := by
  induction jobs generalizing v with
  | nil => exact ⟨v, 1, rfl, le_rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons j jobs ih =>
      have hn := List.nodup_cons.mp hdst
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := ih hn.2 v (fun k hk => houtput k (List.mem_cons_of_mem j hk))
      let C : Stacks T A := { S with R := binaryResizeBatchBank S.R rg W x jobs }
      have keep (i : Fin 9) (hi : i ≠ 3) : C.R (rg j i) = S.R (rg j i) := by
        apply binaryResizeBatchBank_keep
        intro hm
        obtain ⟨k, _, he⟩ := List.mem_map.mp hm
        exact hseparate j i hi k he.symm
      obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryResizeCopy_exec body (rg j) (hrg j) (M j) (L j) (W j) (x j)
        (hW j) (hx j) v₁ C ((keep 0 (by decide)).trans (hwidth j))
        ((keep 1 (by decide)).trans (hvalue j))
        (fun i hi0 hi1 hi3 => (keep i hi3).trans (hblank j i hi0 hi1 hi3))
      have hc : C.R (rg j 3) = [] := by
        rw [show C.R = binaryResizeBatchBank S.R rg W x jobs from rfl,
          binaryResizeBatchBank_keep S.R rg W x jobs (rg j 3) hn.1]
        exact houtput j (by simp)
      rw [hc, List.append_nil] at he₂
      exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
