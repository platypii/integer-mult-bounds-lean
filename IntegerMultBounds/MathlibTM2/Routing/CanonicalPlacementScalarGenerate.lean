module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPlacementReady
public import IntegerMultBounds.MathlibTM2.Routing.HeaderScalarGenerate

/-! Complete the placement operands: shortest dimension and payload words,
and the one-row control. Original padded inputs and copy scratch survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalPlacementScalarCore : Fin 49 → Fin 53 := Fin.castLE (by decide)
def canonicalPlacementScalarSlot : Fin 5 → Fin 53 := ![0,52,50,43,44]
theorem canonicalPlacementScalarCore_injective : Function.Injective canonicalPlacementScalarCore := by decide +kernel
theorem canonicalPlacementScalarSlot_injective : Function.Injective canonicalPlacementScalarSlot := by decide +kernel

def canonicalPlacementScalarProgram (rg : Fin 53 → Fin T) (k : Fin 3) : Pr P T Q A U :=
  .seq (canonicalPlacementResizeProgram (rg ∘ canonicalPlacementScalarCore) k)
    (.seq (headerScalarGenerateProgram (rg ∘ canonicalPlacementScalarSlot))
      (binaryCanonicalCopyProgram (rg 49) (rg 51) (rg 43) (rg 44)))

def canonicalPlacementScalarBank (R : Fin T → List (Fin (A+4))) (rg : Fin 53 → Fin T)
    (L n B : ℕ) (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) :=
  Function.update (headerScalarBank
    (canonicalPlacementResizedBank R (rg ∘ canonicalPlacementScalarCore) L n hlarge k)
    (rg ∘ canonicalPlacementScalarSlot) n) (rg 51) (binSyms (canonicalScalarWidth B) B)

theorem canonicalPlacementScalar_exec (body : P → Pr P T Q A U)
    (rg : Fin 53 → Fin T) (hrg : Function.Injective rg) (L Lb n B : ℕ)
    (hn : n < 2^L) (hB : B < 2^Lb) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L) (k : Fin 3)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hpayload : S.R (rg 49) = binSyms Lb B)
    (hblank : ∀ i : Fin 53, i ≠ 0 → i ≠ 9 → i ≠ 49 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 92*L*L+572*L+529 + binaryResizeBatchCost (fun _ : Fin 9 => L) (fun _ => L)
        (fun _ => canonicalScalarWidth n) (List.finRange 9) + (10*L+13) + (10*Lb+12) ∧
      Exec body (canonicalPlacementScalarProgram rg k) (mk v S) m
        (mk v' { S with R := canonicalPlacementScalarBank S.R rg L n B hlarge k }) := by
  let core := rg ∘ canonicalPlacementScalarCore
  have hc : Function.Injective core := hrg.comp canonicalPlacementScalarCore_injective
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalPlacementResize_exec body core hc L n hn hlarge hdivisor k v S
    hdimension (by
      intro i h0 h9
      apply hblank
      · intro h; exact h0 (Fin.ext (congrArg (fun x : Fin 53 => x.val) h))
      · intro h; exact h9 (Fin.ext (congrArg (fun x : Fin 53 => x.val) h))
      · intro h
        have hv := congrArg (fun x : Fin 53 => x.val) h
        change i.val = 49 at hv
        have := i.isLt
        omega)
  let C : Stacks T A := { S with R := canonicalPlacementResizedBank S.R core L n hlarge k }
  have old (i : Fin 49) (hi : i ∈ ([0,43,44,48] : List (Fin 49))) : C.R (core i) = S.R (core i) :=
    canonicalPlacementResizedBank_copyReady S.R core hc L n hlarge k i hi
  have new (i : Fin 53) (hi : 49 ≤ i.val) : C.R (rg i) = S.R (rg i) := by
    apply canonicalPlacementResizedBank_outside
    intro j he
    have hv := congrArg (fun x : Fin 53 => x.val) (hrg he)
    change j.val = i.val at hv
    have := j.isLt
    omega
  obtain ⟨v₂,hu₂,he₂⟩ := headerScalarGenerate_exec body (rg ∘ canonicalPlacementScalarSlot)
    (hrg.comp canonicalPlacementScalarSlot_injective) L n hn v₁ C
    ((old 0 (by simp)).trans hdimension) (by
      intro i h0
      fin_cases i
      · exact (h0 rfl).elim
      · exact (new 52 (by decide)).trans (hblank 52 (by decide) (by decide) (by decide))
      · exact (new 50 (by decide)).trans (hblank 50 (by decide) (by decide) (by decide))
      · exact (old 43 (by simp)).trans (hblank 43 (by decide) (by decide) (by decide))
      · exact (old 44 (by simp)).trans (hblank 44 (by decide) (by decide) (by decide)))
  let D : Stacks T A := { C with R := headerScalarBank C.R (rg ∘ canonicalPlacementScalarSlot) n }
  have keep (i : Fin 53) (hi : i ≠ 50 ∧ i ≠ 52) : D.R (rg i) = C.R (rg i) := by
    simp [D,headerScalarBank,canonicalPlacementScalarSlot,hrg.eq_iff,hi.1,hi.2]
  obtain ⟨v₃,hu₃,he₃⟩ := binaryCanonicalWordCopy_exec body (rg 49) (rg 51) (rg 43) (rg 44)
    (by simp [List.nodup_cons,hrg.eq_iff]) Lb B hB v₂ D
    ((keep 49 (by decide)).trans ((new 49 (by decide)).trans hpayload))
    ((keep 51 (by decide)).trans ((new 51 (by decide)).trans (hblank 51 (by decide) (by decide) (by decide))))
    ((keep 43 (by decide)).trans ((old 43 (by simp)).trans (hblank 43 (by decide) (by decide) (by decide))))
    ((keep 44 (by decide)).trans ((old 44 (by simp)).trans (hblank 44 (by decide) (by decide) (by decide))))
  refine ⟨v₃,m₁+((10*L+13)+(10*Lb+12)),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  omega

end IntegerMultBounds.MathlibTM2.Routing
