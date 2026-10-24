module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairKeyGenerate
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalSum

/-! Complete the numeric repair operands by computing the physical block width
from original dimension and payload words, preserving all earlier metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalRepairBlockCore : Fin 127 → Fin 130 := Fin.castLE (by decide)
theorem canonicalRepairBlockCore_injective : Function.Injective canonicalRepairBlockCore := by decide +kernel
def canonicalRepairBlockSlot : Fin 10 → Fin 130 := ![0,120,118,128,129,127,40,41,42,45]
theorem canonicalRepairBlockSlot_injective : Function.Injective canonicalRepairBlockSlot := by decide +kernel

def canonicalRepairBlockGenerateProgram (rg : Fin 130 → Fin T) : Pr P T Q A U :=
  .seq (canonicalRepairKeyGenerateProgram (rg ∘ canonicalRepairBlockCore))
    (binaryCanonicalSumProgram (rg ∘ canonicalRepairBlockSlot))

def canonicalRepairBlockGeneratedBank (R : Fin T → List (Fin (A+4)))
    (rg : Fin 130 → Fin T) (L n r B : ℕ) :=
  Function.update (canonicalRepairKeyGeneratedBank R (rg ∘ canonicalRepairBlockCore) L n r B)
    (rg 127) (binSyms (canonicalScalarWidth (n+B+1)) (n+B+1))

theorem canonicalRepairBlockGeneratedBank_block (R : Fin T → List (Fin (A+4)))
    (rg : Fin 130 → Fin T) (L n B : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (wm wp wk : ℕ) :
    canonicalRepairBlockGeneratedBank R rg L n r.val B (rg 127) =
      canonicalRepairPayload (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
        0 (canonicalScalarWidth 1) (canonicalScalarWidth (n+B+1)) wm wp wk 1 B (.inl .block) := by
  simp only [canonicalRepairBlockGeneratedBank,Function.update_self,canonicalRepairPayload]
  rw [canonicalRepair_keyLen n hlarge r]
  congr 1; omega

theorem canonicalRepairBlockGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (L Lb n B : ℕ)
    (hn : n < 2^L) (hB : B < 2^Lb) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hpayload : S.R (rg 120) = binSyms Lb B)
    (hblank : ∀ i : Fin 130, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalClassifierGeneratePrice L W p + 10*W+13 +
        (4*W*(p.wc+p.wy)+22*W+8*(p.wc+p.wy)+24) +
        (L*(4*n+11)+8*n+13) + (18*L+39) + (10*Lb+12) + (44*(L+Lb)+99) ∧
      Exec body (canonicalRepairBlockGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalRepairBlockGeneratedBank S.R rg L n r.val B }) := by
  dsimp only
  let core := rg ∘ canonicalRepairBlockCore
  have hc : Function.Injective core := hrg.comp canonicalRepairBlockCore_injective
  have cb : ∀ i : Fin 127, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (core i) = [] := by
    intro i h0 h9 h18 h120
    exact hblank _ (fun h => h0 (Fin.ext (congrArg (fun x : Fin 130 => x.val) h)))
      (fun h => h9 (Fin.ext (congrArg (fun x : Fin 130 => x.val) h)))
      (fun h => h18 (Fin.ext (congrArg (fun x : Fin 130 => x.val) h)))
      (fun h => h120 (Fin.ext (congrArg (fun x : Fin 130 => x.val) h)))
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalRepairKeyGenerate_exec body core hc L Lb n B hn hB
    hlarge hdivisor r v S hdimension hresidue hpayload cb
  let count := core ∘ canonicalRepairKeyCore
  have hcount : Function.Injective count := hc.comp canonicalRepairKeyCore_injective
  let C : Stacks T A := { S with R := canonicalRepairKeyGeneratedBank S.R core L n r.val B }
  have keep (i : Fin 125) : C.R (count i) = canonicalRepairCountGeneratedBank S.R count L n r.val (count i) := by
    have hi := i.isLt
    have h125 : canonicalRepairKeyCore i ≠ 125 := by intro h; have := congrArg Fin.val h; change i.val = 125 at this; omega
    have h126 : canonicalRepairKeyCore i ≠ 126 := by intro h; have := congrArg Fin.val h; change i.val = 126 at this; omega
    simp [C,canonicalRepairKeyGeneratedBank,count,hc.eq_iff,h125,h126]
  have newBlank (i : Fin 130) (hi : 127 ≤ i.val) : C.R (rg i) = [] := by
    have off : ∀ j : Fin 127, core j ≠ rg i := by
      intro j he
      have hv := congrArg (fun x : Fin 130 => x.val) (hrg he)
      change j.val = i.val at hv
      have := j.isLt
      omega
    change canonicalRepairKeyGeneratedBank S.R core L n r.val B (rg i) = []
    rw [show canonicalRepairKeyGeneratedBank S.R core L n r.val B (rg i) =
        canonicalRepairCountGeneratedBank S.R count L n r.val (rg i) from by
      simp [canonicalRepairKeyGeneratedBank,count,(off 125).symm,(off 126).symm]]
    rw [canonicalRepairCountGeneratedBank_outside S.R count L n r.val _ (fun j => off _)]
    apply hblank <;> intro h <;> subst i <;> norm_num at hi
  have countBlank : ∀ i : Fin 125, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (count i) = [] := by
    intro i h0 h9 h18 h120
    apply cb <;> intro h
    · exact h0 (Fin.ext (congrArg (fun x : Fin 127 => x.val) h))
    · exact h9 (Fin.ext (congrArg (fun x : Fin 127 => x.val) h))
    · exact h18 (Fin.ext (congrArg (fun x : Fin 127 => x.val) h))
    · exact h120 (Fin.ext (congrArg (fun x : Fin 127 => x.val) h))
  have scratch (i : Fin 118) (hi : i ∈ ([39,40,41,42,43,45] : List (Fin 118))) :
      C.R (count ⟨i.val,by have := i.isLt; omega⟩) = [] :=
    (keep _).trans (canonicalRepairCountGeneratedBank_scratch S.R count hcount L n r.val countBlank i hi)
  obtain ⟨v₂,hu₂,he₂⟩ := binaryCanonicalSum_exec body (rg ∘ canonicalRepairBlockSlot)
    (hrg.comp canonicalRepairBlockSlot_injective) L Lb n B hn hB v₁ C
    ((keep 0).trans ((canonicalRepairCountGeneratedBank_dimension S.R count hcount L n r.val).trans hdimension))
    ((keep 120).trans ((canonicalRepairCountGeneratedBank_payload S.R count hcount L n r.val).trans hpayload))
    (by
      change (C.R (count 118)).length = 1
      rw [keep 118,canonicalRepairCountGeneratedBank_one S.R count hcount L n r.val]
      rfl)
    (by
      intro i h0 h1 h2
      fin_cases i
      · exact (h0 rfl).elim
      · exact (h1 rfl).elim
      · exact (h2 rfl).elim
      · exact newBlank 128 (by decide)
      · exact newBlank 129 (by decide)
      · exact newBlank 127 (by decide)
      · exact scratch 40 (by simp)
      · exact scratch 41 (by simp)
      · exact scratch 42 (by simp)
      · exact scratch 45 (by simp))
  refine ⟨v₂,m₁+(44*(L+Lb)+99),hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  omega

end
end IntegerMultBounds.MathlibTM2.Routing
