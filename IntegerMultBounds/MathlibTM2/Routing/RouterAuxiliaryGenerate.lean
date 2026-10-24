module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeCopy
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalWord
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalOuterInput
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStageWidths

/-! Generate the live-profile count and the width-conversion operands together.
Original count, index-width and target-width words survive; scratch restores. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerAuxiliaryResizeSlot : Fin 9 → Fin 12 := ![1,0,6,3,7,8,9,10,11]
theorem routerAuxiliaryResizeSlot_injective : Function.Injective routerAuxiliaryResizeSlot := by decide +kernel

def routerAuxiliaryGenerateProgram (rg : Fin 12 → Fin T) : Pr P T Q A U :=
  .seq (binaryResizeCopyProgram (rg ∘ routerAuxiliaryResizeSlot))
    (.seq (binaryCanonicalCopyProgram (rg 2) (rg 4) (rg 9) (rg 10))
      (.act (Action.push (.rt (rg 5)) (fun _ => bitSymbol true) .done)))

def routerAuxiliaryBank (R : Fin T → List (Fin (A+4))) (rg : Fin 12 → Fin T) (W n wy : ℕ) :=
  Function.update (Function.update (Function.update R (rg 3) (binSyms W n))
    (rg 4) (binSyms (canonicalScalarWidth wy) wy)) (rg 5) [bitSymbol true]

def routerAuxiliaryProfileSource (i : Fin 7) : Fin 12 := if i = 0 then 3 else 6
def routerAuxiliaryWidthSource (i : Fin 6) : Fin 12 := if i = 0 then 5 else if i = 1 then 4 else 6

theorem routerAuxiliaryBank_profile (R : Fin T → List (Fin (A+4)))
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (W n wy : ℕ)
    (hblank : R (rg 6) = []) (i : Fin 7) :
    routerAuxiliaryBank R rg W n wy (rg (routerAuxiliaryProfileSource i)) =
      if i = 0 then binSyms W n else [] := by
  by_cases hi : i = 0
  · subst i; simp [routerAuxiliaryBank,routerAuxiliaryProfileSource,hrg.eq_iff]
  · simp [routerAuxiliaryBank,routerAuxiliaryProfileSource,hi,hrg.eq_iff,hblank]

theorem routerAuxiliaryBank_width (R : Fin T → List (Fin (A+4)))
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (W n wy : ℕ)
    (hblank : R (rg 6) = []) (i : Fin 6) :
    routerAuxiliaryBank R rg W n wy (rg (routerAuxiliaryWidthSource i)) =
      if i = 0 then binSyms (canonicalScalarWidth 1) 1
      else if i = 1 then binSyms (canonicalScalarWidth wy) wy else [] := by
  fin_cases i <;> simp [routerAuxiliaryBank,routerAuxiliaryWidthSource,hrg.eq_iff,hblank]
  rfl

theorem routerAuxiliaryGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (M L Ly W n wy : ℕ)
    (hW : W < 2^M) (hn : n < 2^L) (hwy : wy < 2^Ly)
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R (rg 0) = binSyms L n) (hwidth : S.R (rg 1) = binSyms M W)
    (htarget : S.R (rg 2) = binSyms Ly wy)
    (hblank : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → i ≠ 2 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 2*M*(4*W+11)+12*L+26*W+42 + (10*Ly+13) ∧
      Exec body (routerAuxiliaryGenerateProgram rg) (mk v S) m
        (mk v' { S with R := routerAuxiliaryBank S.R rg W n wy }) := by
  have sep : ∀ i : Fin 9, i ≠ 0 → i ≠ 1 → i ≠ 3 →
      routerAuxiliaryResizeSlot i ≠ 0 ∧ routerAuxiliaryResizeSlot i ≠ 1 ∧ routerAuxiliaryResizeSlot i ≠ 2 := by
    decide +kernel
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := binaryResizeCopy_exec body (rg ∘ routerAuxiliaryResizeSlot)
    (hrg.comp routerAuxiliaryResizeSlot_injective) M L W n hW hn v S hwidth hcount (by
      intro i h0 h1 h3
      have h := sep i h0 h1 h3
      exact hblank _ h.1 h.2.1 h.2.2)
  have hd : S.R ((rg ∘ routerAuxiliaryResizeSlot) 3) = [] := hblank 3 (by decide) (by decide) (by decide)
  rw [hd,List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms W n) }
  obtain ⟨v₂,hu₂,he₂⟩ := binaryCanonicalWordCopy_exec body (rg 2) (rg 4) (rg 9) (rg 10)
    (by simp [List.nodup_cons,hrg.eq_iff]) Ly wy hwy v₁ C
    (by simpa [C,hrg.eq_iff] using htarget)
    (by simp [C,hrg.eq_iff,hblank 4 (by decide) (by decide) (by decide)])
    (by simp [C,hrg.eq_iff,hblank 9 (by decide) (by decide) (by decide)])
    (by simp [C,hrg.eq_iff,hblank 10 (by decide) (by decide) (by decide)])
  let D : Stacks T A := { C with R := Function.update C.R (rg 4) (binSyms (canonicalScalarWidth wy) wy) }
  have hp : (Action.push (.rt (rg 5)) (fun _ => bitSymbol true) .done : Act T Q A U).run (mk v₂ D) =
      mk v₂ { D with R := Function.update D.R (rg 5) [bitSymbol true] } := by
    simp [Action.run,update_rt,D,C,hrg.eq_iff,hblank 5 (by decide) (by decide) (by decide)]
  have he₃ := hp ▸ Exec.act (body := body) _ (mk v₂ D)
  refine ⟨v₂,m₁+((10*Ly+12)+1),hu₂.trans hu₁,?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  omega

end IntegerMultBounds.MathlibTM2.Routing
