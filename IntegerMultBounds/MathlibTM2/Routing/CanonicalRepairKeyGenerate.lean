module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairCountReady
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalSuccessor
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairDimensions

/-! Generate exact key-length and payload operands after repair zero/count setup.
Only original dimension, residue and payload-width words are supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalRepairKeyCore : Fin 125 → Fin 127 := Fin.castLE (by decide)
theorem canonicalRepairKeyCore_injective : Function.Injective canonicalRepairKeyCore := by decide +kernel
def canonicalRepairKeySlot : Fin 6 → Fin 127 := ![0,118,125,40,41,9]
theorem canonicalRepairKeySlot_injective : Function.Injective canonicalRepairKeySlot := by decide +kernel

def canonicalRepairKeyGenerateProgram (rg : Fin 127 → Fin T) : Pr P T Q A U :=
  .seq (canonicalRepairCountGenerateProgram (rg ∘ canonicalRepairKeyCore))
    (.seq (binaryCanonicalSuccessorProgram (rg ∘ canonicalRepairKeySlot))
      (binaryCanonicalCopyProgram (rg 120) (rg 126) (rg 40) (rg 41)))

def canonicalRepairKeyGeneratedBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 127 → Fin T) (L n r B : ℕ) :=
  Function.update (Function.update
    (canonicalRepairCountGeneratedBank R (rg ∘ canonicalRepairKeyCore) L n r)
    (rg 125) (binSyms (canonicalScalarWidth (n+1)) (n+1)))
    (rg 126) (binSyms (canonicalScalarWidth B) B)

theorem canonicalRepairKeyGeneratedBank_payload (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 127 → Fin T) (L n r B : ℕ) :
    canonicalRepairKeyGeneratedBank R rg L n r B (rg 126) = binSyms (canonicalScalarWidth B) B := by
  exact Function.update_self _ _ _

theorem canonicalRepairKeyGeneratedBank_key (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 127 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n)) (wb wm wp : ℕ) :
    canonicalRepairKeyGeneratedBank R rg L n r.val B (rg 125) =
      canonicalRepairPayload (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
        0 (canonicalScalarWidth 1) wb wm wp (canonicalScalarWidth (n+1)) 1 B (.inr .keyLength) := by
  rw [canonicalRepair_keyWord n hlarge r]
  simp [canonicalRepairKeyGeneratedBank,hrg.eq_iff]

theorem canonicalRepairKeyGeneratedBank_records (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 127 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n)) (wb wp wk : ℕ) :
    canonicalRepairKeyGeneratedBank R rg L n r.val B (rg 124) =
      canonicalRepairPayload (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
        0 (canonicalScalarWidth 1) wb (n+1) wp wk 1 B (.inl .records) := by
  rw [canonicalRepair_countWord n hlarge r]
  simp [canonicalRepairKeyGeneratedBank,canonicalRepairCountGeneratedBank,canonicalRepairKeyCore,hrg.eq_iff]

theorem canonicalRepairKeyGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 127 → Fin T) (hrg : Function.Injective rg) (L Lb n B : ℕ)
    (hn : n < 2 ^ L) (hB : B < 2 ^ Lb) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hpayload : S.R (rg 120) = binSyms Lb B)
    (hblank : ∀ i : Fin 127, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalClassifierGeneratePrice L W p + 10 * W + 13 +
        (4 * W * (p.wc+p.wy) + 22 * W + 8 * (p.wc+p.wy) + 24) +
        (L * (4 * n + 11) + 8 * n + 13) + (18*L+39) + (10*Lb+12) ∧
      Exec body (canonicalRepairKeyGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalRepairKeyGeneratedBank S.R rg L n r.val B }) := by
  dsimp only
  let core := rg ∘ canonicalRepairKeyCore
  have hc : Function.Injective core := hrg.comp canonicalRepairKeyCore_injective
  have cb : ∀ i : Fin 125, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (core i) = [] := by
    intro i h0 h9 h18 h120
    exact hblank _ (fun h => h0 (Fin.ext (congrArg (fun x : Fin 127 => x.val) h)))
      (fun h => h9 (Fin.ext (congrArg (fun x : Fin 127 => x.val) h)))
      (fun h => h18 (Fin.ext (congrArg (fun x : Fin 127 => x.val) h)))
      (fun h => h120 (Fin.ext (congrArg (fun x : Fin 127 => x.val) h)))
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalRepairCountGenerate_exec body core hc L n hn hlarge hdivisor
    r v S hdimension hresidue cb
  let C : Stacks T A := { S with R := canonicalRepairCountGeneratedBank S.R core L n r.val }
  have scratch (i : Fin 118) (hi : i ∈ ([39,40,41,42,43,45] : List (Fin 118))) :
      C.R (core ⟨i.val,by have := i.isLt; omega⟩) = [] :=
    canonicalRepairCountGeneratedBank_scratch S.R core hc L n r.val cb i hi
  have newBlank (i : Fin 127) (hi : 125 ≤ i.val) : C.R (rg i) = [] := by
    rw [show C.R (rg i) = S.R (rg i) from canonicalRepairCountGeneratedBank_outside S.R core L n r.val _ (by
      intro j he
      have hv := congrArg (fun x : Fin 127 => x.val) (hrg he)
      change j.val = i.val at hv
      have := j.isLt
      omega)]
    apply hblank <;> intro h <;> subst i <;> norm_num at hi
  obtain ⟨v₂,hu₂,he₂⟩ := binaryCanonicalSuccessor_exec body (rg ∘ canonicalRepairKeySlot)
    (hrg.comp canonicalRepairKeySlot_injective) L n hn v₁ C
    ((canonicalRepairCountGeneratedBank_dimension S.R core hc L n r.val).trans hdimension)
    (by
      change (C.R (rg 118)).length = 1
      rw [show C.R (rg 118) = [bitSymbol true] from canonicalRepairCountGeneratedBank_one S.R core hc L n r.val]
      rfl)
    (by
      intro i h0 h1 h5
      fin_cases i
      · exact (h0 rfl).elim
      · exact (h1 rfl).elim
      · exact newBlank 125 (by decide)
      · exact scratch 40 (by simp)
      · exact scratch 41 (by simp)
      · exact (h5 rfl).elim)
  let D : Stacks T A := { C with R := Function.update C.R (rg 125) (binSyms (canonicalScalarWidth (n+1)) (n+1)) }
  have keepD (i : Fin 127) (hi : i ≠ 125) : D.R (rg i) = C.R (rg i) := by simp [D,hrg.eq_iff,hi]
  have sourceB : D.R (rg 120) = binSyms Lb B :=
    (keepD 120 (by decide)).trans ((canonicalRepairCountGeneratedBank_payload S.R core hc L n r.val).trans hpayload)
  obtain ⟨v₃,hu₃,he₃⟩ := binaryCanonicalWordCopy_exec body (rg 120) (rg 126) (rg 40) (rg 41)
    (by simp [List.nodup_cons,hrg.eq_iff]) Lb B hB v₂ D sourceB
    ((keepD 126 (by decide)).trans (newBlank 126 (by decide)))
    ((keepD 40 (by decide)).trans (scratch 40 (by simp)))
    ((keepD 41 (by decide)).trans (scratch 41 (by simp)))
  refine ⟨v₃,m₁+((18*L+39)+(10*Lb+12)),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  nlinarith only [hm₁]

end
end IntegerMultBounds.MathlibTM2.Routing
