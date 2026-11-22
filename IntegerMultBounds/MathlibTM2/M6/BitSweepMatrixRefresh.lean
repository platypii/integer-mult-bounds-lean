module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepRankEvaluation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix

/-! Refresh just the two destination rows of the rank evaluator's matrix tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Cover.Fallback Shared50ModularControl Host Stack Mult.PhaseCellToeplitz
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

def destinationRows {M : ℕ} [NeZero M] (A H : ℕ) (mat : Matrix (Fin 64) (Fin 64) (ZMod M)) :=
  matrixWords A H (mat.submatrix (fun i : Fin 2 => i.castLE (by decide)) id)

private theorem matrixWords_split {M : ℕ} [NeZero M] (A H : ℕ)
    (mat : Matrix (Fin 64) (Fin 64) (ZMod M)) :
    matrixWords A H mat = destinationRows A H mat ++
      matrixWords A H (mat.submatrix (Fin.natAdd 2 : Fin 62 → Fin 64) id) := by
  let row := fun i : Fin 64 => (List.ofFn fun j => binSyms (A := A) H (mat i j).val).flatten
  change (List.ofFn row).flatten = _
  rw [List.ofFn_add (m := 62) (n := 2),List.flatten_append]
  rfl

theorem destinationRows_length {M : ℕ} [NeZero M] (A H : ℕ)
    (mat : Matrix (Fin 64) (Fin 64) (ZMod M)) :
    (destinationRows A H mat).length = 128*H := by
  have size {d e : ℕ} (m : Matrix (Fin d) (Fin e) (ZMod M)) : (matrixWords A H m).length = d*(e*H) := by
    simp [matrixWords,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const]
  exact (size _).trans (by ring)

/-- The chart tape is shared by every destination. -/
theorem sweepRankMatrices_chart (w : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (n : Fin 9) (r : Role) (i j : Fin ((prime^w)^128)) :
    sweepRankMatrices w parent n r i false = sweepRankMatrices w parent n r j false := by simp only [sweepRankMatrices,Bool.false_eq_true,↓reduceIte]

private theorem sweepRankMatrices_suffix (w : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (n : Fin 9) (r : Role) (i j : Fin ((prime^w)^128)) :
    ((sweepRankMatrices w parent n r i true).submatrix (Fin.natAdd 2 : Fin 62 → Fin 64) id) =
      ((sweepRankMatrices w parent n r j true).submatrix (Fin.natAdd 2 : Fin 62 → Fin 64) id) := by
  ext a b
  have h₀ : Fin.natAdd 2 a ≠ 0 := by intro eqn; have := congrArg Fin.val eqn; simp at this
  have h₁ : Fin.natAdd 2 a ≠ 1 := by intro eqn; have := congrArg Fin.val eqn; simp at this; omega
  change sweepRankMatrices w parent n r i true (Fin.natAdd 2 a) b = sweepRankMatrices w parent n r j true (Fin.natAdd 2 a) b
  simp only [sweepRankMatrices,↓reduceIte,h₀,h₁]

def refreshSweepMatrix {T Q A : ℕ} {P U : Type} (r : Fin 6 ↪ Fin T) : Pr P T Q A U :=
  .seq (movePrefix (r 0) (r 1) (r 2) (r 4) (r 5)) (movePrefix (r 0) (r 3) (r 1) (r 4) (r 5))

/-- Install the next destination, saving the old rows and preserving the
parent, translation and borrowed tape suffix. The same code works in reverse
with the input and saved-row registers exchanged. -/
theorem refreshSweepMatrix_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (regs : Fin 6 ↪ Fin T) (w H : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (n : Fin 9) (r : Role) (i j : Fin ((prime^w)^128)) (u : HS T Q A U) (S : Stacks T A)
    (tail rest : List (Fin (A+4))) :
    let mat := fun d => sweepRankMatrices w parent n r d true
    (S.R (regs 0)).length = 128*H → S.R (regs 1) = matrixWords A H (mat i) ++ tail →
    S.R (regs 3) = destinationRows A H (mat j) ++ rest →
    S.R (regs 4) = [] → S.R (regs 5) = [] →
    ∃ z, z.user = u.user ∧ Exec body (refreshSweepMatrix regs) (mk u S) (12*(128*H)+12)
      (mk z {S with R := Function.update (Function.update (Function.update S.R (regs 2)
        (destinationRows A H (mat i) ++ S.R (regs 2))) (regs 3) rest) (regs 1) (matrixWords A H (mat j) ++ tail)}) := by
  intro mat clock input next saved tmp
  let lower := fun d => matrixWords A H ((mat d).submatrix (Fin.natAdd 2 : Fin 62 → Fin 64) id)
  have split (d) : matrixWords A H (mat d) = destinationRows A H (mat d) ++ lower d := matrixWords_split ..
  have suffix : lower i = lower j := congrArg (matrixWords A H) (sweepRankMatrices_suffix w parent n r i j)
  obtain ⟨v,user,save⟩ := movePrefix_exec (body := body) (count := regs 0) (src := regs 1) (dst := regs 2)
    (saved := regs 4) (tmp := regs 5) (by simp [List.nodup_cons,regs.injective.eq_iff])
    (destinationRows A H (mat i)) (lower i ++ tail) u S (by rw [input,split,List.append_assoc])
    (by rw [clock,destinationRows_length]) saved tmp
  let B := {S with
    R := Function.update (Function.update S.R (regs 1) (lower i ++ tail)) (regs 2)
      (destinationRows A H (mat i) ++ S.R (regs 2))}
  obtain ⟨z,hz,install⟩ := movePrefix_exec (body := body) (count := regs 0) (src := regs 3) (dst := regs 1)
    (saved := regs 4) (tmp := regs 5) (by simp [List.nodup_cons,regs.injective.eq_iff])
    (destinationRows A H (mat j)) rest v B (by simpa [B] using next)
    (by simp [B,clock,destinationRows_length]) (by simpa [B] using saved) (by simpa [B] using tmp)
  refine ⟨z,hz.trans user,(Exec.seq save install).cast (by simp only [destinationRows_length]; omega) ?_⟩
  apply congrArg (mk z)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases a : k = regs 1 <;> by_cases b : k = regs 2 <;> by_cases c : k = regs 3 <;>
    simp_all [B,List.append_assoc]

end IntegerMultBounds.MathlibTM2.M6.BitNode
