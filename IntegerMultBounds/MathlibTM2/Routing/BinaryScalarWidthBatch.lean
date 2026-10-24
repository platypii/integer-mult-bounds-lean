module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryScalarWidth

/-! Generate a fixed bank of exact scalar widths while sharing traversal
scratch. Numeric dimensions occur only in the execution and cost ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U J : Type}

def binaryScalarWidthBatchProgram (rg : J → Fin 6 → Fin T) : List J → Pr P T Q A U
  | [] => .act .done
  | j :: jobs => .seq (binaryScalarWidthBatchProgram rg jobs) (binaryScalarWidthProgram (rg j))

def binaryScalarWidthBatchBank (R : Fin T → List (Fin (A + 4)))
    (rg : J → Fin 6 → Fin T) (L x : J → ℕ) : List J → Fin T → List (Fin (A + 4))
  | [] => R
  | j :: jobs => Function.update (binaryScalarWidthBatchBank R rg L x jobs) (rg j 2)
      (binSyms (L j) (Nat.clog 2 (x j + 1)))

def binaryScalarWidthBatchCost (L : J → ℕ) : List J → ℕ
  | [] => 1
  | j :: jobs => binaryScalarWidthBatchCost L jobs + (4 * L j * L j + 26 * L j + 22)

theorem binaryScalarWidthBatchBank_keep (R : Fin T → List (Fin (A + 4)))
    (rg : J → Fin 6 → Fin T) (L x : J → ℕ) (jobs : List J) (k : Fin T)
    (hk : k ∉ jobs.map (fun j => rg j 2)) :
    binaryScalarWidthBatchBank R rg L x jobs k = R k := by
  induction jobs with
  | nil => rfl
  | cons j jobs ih =>
      rw [binaryScalarWidthBatchBank,Function.update_of_ne (by intro he; exact hk (by simp [he]))]
      exact ih (fun hm => hk (by simp [hm]))

theorem binaryScalarWidthBatchBank_at (R : Fin T → List (Fin (A + 4)))
    (rg : J → Fin 6 → Fin T) (L x : J → ℕ) (jobs : List J)
    (hdst : (jobs.map (fun j => rg j 2)).Nodup) (j : J) (hj : j ∈ jobs) :
    binaryScalarWidthBatchBank R rg L x jobs (rg j 2) = binSyms (L j) (Nat.clog 2 (x j + 1)) := by
  induction jobs with
  | nil => simp at hj
  | cons k jobs ih =>
      have hn := List.nodup_cons.mp hdst
      rcases List.mem_cons.mp hj with rfl | hj
      · simp [binaryScalarWidthBatchBank]
      · have hne : rg j 2 ≠ rg k 2 := by
          intro he
          exact hn.1 (List.mem_map.mpr ⟨j,hj,he⟩)
        rw [binaryScalarWidthBatchBank,Function.update_of_ne hne]
        exact ih hn.2 hj

theorem binaryScalarWidthBatch_exec (body : P → Pr P T Q A U)
    (rg : J → Fin 6 → Fin T) (hrg : ∀ j, Function.Injective (rg j))
    (L x : J → ℕ) (hx : ∀ j, x j < 2 ^ L j) (jobs : List J)
    (hdst : (jobs.map (fun j => rg j 2)).Nodup)
    (hseparate : ∀ j i, i ≠ 2 → ∀ k, rg j i ≠ rg k 2)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : ∀ j, S.R (rg j 0) = binSyms (L j) (x j))
    (hblank : ∀ j i, i ≠ 0 → i ≠ 5 → S.R (rg j i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ binaryScalarWidthBatchCost L jobs ∧
      Exec body (binaryScalarWidthBatchProgram rg jobs) (mk v S) m
        (mk v' { S with R := binaryScalarWidthBatchBank S.R rg L x jobs }) := by
  induction jobs generalizing v with
  | nil => exact ⟨v,1,rfl,le_rfl,Exec.act (body := body) .done (mk v S)⟩
  | cons j jobs ih =>
      have hn := List.nodup_cons.mp hdst
      obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := ih hn.2 v
      let C : Stacks T A := { S with R := binaryScalarWidthBatchBank S.R rg L x jobs }
      have keep (i : Fin 6) (hi : i ≠ 2) : C.R (rg j i) = S.R (rg j i) := by
        apply binaryScalarWidthBatchBank_keep
        intro hm
        obtain ⟨k,_,he⟩ := List.mem_map.mp hm
        exact hseparate j i hi k he.symm
      obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := binaryScalarWidth_exec body (rg j) (hrg j) (L j) (x j)
        (hx j) v₁ C ((keep 0 (by decide)).trans (hsrc j)) (by
          intro i h0 h5
          by_cases h2 : i = 2
          · subst i
            rw [show C.R = binaryScalarWidthBatchBank S.R rg L x jobs from rfl,
              binaryScalarWidthBatchBank_keep S.R rg L x jobs _ hn.1]
            exact hblank j 2 (by decide) (by decide)
          · exact (keep i h2).trans (hblank j i h0 h5))
      exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
