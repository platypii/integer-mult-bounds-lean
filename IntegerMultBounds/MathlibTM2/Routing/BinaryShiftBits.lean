module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! A fixed bit list describes a small arithmetic circuit of binary shifts.
The structural proof applies to every width and initial value. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryShiftBitsProgram (dst tmp : Fin T) : List Bool → Pr P T Q A U
  | [] => .act .done
  | b :: bs => .seq (bshift dst tmp (fun _ => bitSymbol b)) (binaryShiftBitsProgram dst tmp bs)

def binaryShiftBitsValue (x : ℕ) (bs : List Bool) : ℕ :=
  bs.foldl (fun x b => 2 * x + b.toNat) x

theorem binaryShiftBits_exec (body : P → Pr P T Q A U)
    (dst tmp : Fin T) (hne : dst ≠ tmp) (bs : List Bool) (L x : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hdst : S.R dst = binSyms L x) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryShiftBitsProgram dst tmp bs) (mk v S) (bs.length * (4 * L + 8) + 1)
        (mk v' { S with R := Function.update S.R dst (binSyms L (binaryShiftBitsValue x bs)) }) := by
  induction bs generalizing x v S with
  | nil =>
      refine ⟨v, rfl, ?_⟩
      have hf : Function.update S.R dst (binSyms L (binaryShiftBitsValue x [])) = S.R := by
        rw [show binaryShiftBitsValue x [] = x from rfl, ← hdst]
        exact Function.update_eq_self _ _
      rw [hf]
      simpa [binaryShiftBitsProgram, Action.run] using
        (Exec.act (body := body) (.done : Act T Q A U) (mk v S))

  | cons b bs ih =>
      obtain ⟨v₁, hu₁, he₁⟩ := bshift_exec (body := body) hne (fun _ => bitSymbol b) v S htmp
      rw [hdst, length_binSyms, binSyms_shift] at he₁
      let C : Stacks T A := { S with R := Function.update S.R dst (binSyms L (2 * x + b.toNat)) }
      obtain ⟨v₂, hu₂, he₂⟩ := ih (2 * x + b.toNat) v₁ C (by simp [C])
        (by simp [C, hne.symm, htmp])
      have hf : ({ C with R := (Function.update C.R dst
          (binSyms L (binaryShiftBitsValue (2 * x + b.toNat) bs))) } : Stacks T A) =
          { S with R := Function.update S.R dst (binSyms L (binaryShiftBitsValue x (b :: bs))) } := by
        simp [C, binaryShiftBitsValue]
      rw [hf] at he₂
      exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by simp only [List.length_cons]; ring) rfl⟩

/-- Build a literal from a width reference without compiling that width into code. -/
theorem binaryLiteral_exec (body : P → Pr P T Q A U)
    (src dst tmp : Fin T) (hreg : [src, dst, tmp].Nodup) (bs : List Bool) (L : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hlen : (S.R src).length = L)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (.seq (bzero src dst tmp) (binaryShiftBitsProgram dst tmp bs)) (mk v S)
        ((4 * L + 4) + (bs.length * (4 * L + 8) + 1))
        (mk v' { S with R := Function.update S.R dst (binSyms L (binaryShiftBitsValue 0 bs)) }) := by
  have hne : dst ≠ tmp := (List.pairwise_cons.mp (List.pairwise_cons.mp hreg).2).1 _ (by simp)
  obtain ⟨v₁, hu₁, he₁⟩ := bzero_exec (body := body) hreg v S htmp
  rw [hlen, hdst, List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update S.R dst (binSyms L 0) }
  obtain ⟨v₂, hu₂, he₂⟩ := binaryShiftBits_exec body dst tmp hne bs L 0 v₁ C (by simp [C])
    (by simp [C, hne.symm, htmp])
  refine ⟨v₂, hu₂.trans hu₁, ?_⟩
  simpa only [C, Function.update_idem] using Exec.seq he₁ he₂

end IntegerMultBounds.MathlibTM2.Routing
