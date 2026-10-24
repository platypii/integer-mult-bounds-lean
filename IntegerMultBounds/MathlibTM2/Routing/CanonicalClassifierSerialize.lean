module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassifierGenerate
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierOperandFrame

/-! Serialize the complete classifier bank from original dimension/residue.
Generated descriptor and classifier operands remain available for cleanup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalClassifierSerializeProgram (rg : Fin 118 → Fin T) (dst : Fin T)
    (delimiter : Fin (A + 4)) : Pr P T Q A U :=
  .seq (canonicalClassifierGenerateProgram rg) (classifierOperandCopy rg dst delimiter)

theorem canonicalClassifierSerialize_exec (body : P → Pr P T Q A U)
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A + 4)) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 118, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    let words := canonicalClassifierOperands p (canonicalScalarWidth p.K) (canonicalScalarWidth p.n)
      (canonicalScalarWidth (p.ρ+1)) (canonicalScalarWidth p.m)
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalClassifierGeneratePrice L W p + 16 * (6 * (L+W) + 7) + 1 ∧
      Exec body (canonicalClassifierSerializeProgram rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update (canonicalClassifierGeneratedBank S.R rg L n r.val)
          dst (classifierOperandFrame delimiter rg words ++ S.R dst)) }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let words := canonicalClassifierOperands (A := A) p (canonicalScalarWidth p.K) (canonicalScalarWidth p.n)
    (canonicalScalarWidth (p.ρ+1)) (canonicalScalarWidth p.m)
  let B := canonicalDescriptorGeneratedBank S.R (rg ∘ canonicalClassifierCore) L n r.val
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalClassifierGenerate_exec body rg hrg L n hn hlarge hdivisor
    r v S hdimension hresidue hblank
  let C : Stacks T A := { S with R := canonicalClassifierGeneratedBank S.R rg L n r.val }
  have baseBlank (i : Fin 118)
      (hi : i ∈ ([39,40,41,42,43,45,108,109,110,111,112,113,114,115,116,117] : List (Fin 118))) :
      B (rg i) = [] := canonicalClassifier_blank S.R rg hrg L n r.val hblank i hi
  have hw (i : Fin 16) : (words i).length ≤ L+W := by
    have hK : canonicalScalarWidth p.K ≤ W := Nat.clog_le_of_le_pow
      (Nat.succ_le_of_lt (canonicalClassifier_raw_fit L n hn r 0))
    have hd : canonicalScalarWidth p.n ≤ L := Nat.clog_le_of_le_pow
      (Nat.succ_le_of_lt (canonicalClassifier_raw_fit L n hn r 2))
    have hr : canonicalScalarWidth (p.ρ+1) ≤ W := Nat.clog_le_of_le_pow
      (Nat.succ_le_of_lt (canonicalClassifier_raw_fit L n hn r 3))
    have ht : canonicalScalarWidth p.m ≤ L := Nat.clog_le_of_le_pow
      (Nat.succ_le_of_lt (canonicalClassifier_raw_fit L n hn r 5))
    fin_cases i <;> simp [words,canonicalClassifierOperands] <;> omega
  have hb := classifierGeneratedBank_operands B rg hrg L W p (baseBlank 39 (by simp))
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := classifierOperandCopy_exec body rg hrg dst hoff delimiter words (L+W)
    hw v₁ C (by intro i; exact congrFun hb i)
    ((classifierGeneratedBank_low B rg hrg L W p 40 (by decide)).trans (baseBlank 40 (by simp)))
    ((classifierGeneratedBank_low B rg hrg L W p 41 (by decide)).trans (baseBlank 41 (by simp)))
  have hk : C.R dst = S.R dst :=
    (classifierGeneratedBank_outside B rg L W p dst hoff).trans
      (canonicalDescriptorGeneratedBank_outside S.R (rg ∘ canonicalClassifierCore) L n r.val dst (fun i => hoff _))
  rw [hk] at he₂
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
