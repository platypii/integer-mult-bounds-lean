module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryZeroField
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairInput

/-! Generate the two shared zero operands for the five repair index fields.
The three borrowed fields reuse one word; the zero-width spectator stays empty. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def repairZeroSlot (j : Fin 2) : BinaryZeroReg → Fin 8
  | .width => if j = 0 then 0 else 1
  | .unary => 4
  | .dst => if j = 0 then 2 else 3
  | .scratch i => ⟨5+i.val,by have := i.isLt; omega⟩

theorem repairZeroSlot_injective (j : Fin 2) : Function.Injective (repairZeroSlot j) := by
  fin_cases j <;> intro a b h <;> cases a <;> cases b
  all_goals first | rfl | skip
  all_goals
    have hv := congrArg (fun i : Fin 8 => i.val) h
    simp [repairZeroSlot] at hv <;> first | omega | (congr 1; apply Fin.ext; omega)

def repairZeroGenerateProgram (rg : Fin 8 → Fin T) : Pr P T Q A U :=
  .seq (binaryZeroFieldProgram (rg ∘ repairZeroSlot 0)) (binaryZeroFieldProgram (rg ∘ repairZeroSlot 1))

def repairZeroBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 8 → Fin T) (p : Par) :=
  Function.update (Function.update R (rg 2) (binSyms p.wc 0)) (rg 3) (binSyms p.wy 0)

def repairZeroSource : Fin 5 → Fin 8 := ![2,3,2,2,4]

theorem repairZeroBank_fields (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg) (p : Par) (hblank : R (rg 4) = []) (f : Fin 5) :
    repairZeroBank R rg p (rg (repairZeroSource f)) = binSyms (selectiveLen p 0 f) 0 := by
  fin_cases f <;> simp [repairZeroBank,repairZeroSource,selectiveLen,hrg.eq_iff,hblank]
  rfl

theorem repairZeroGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg) (W : ℕ) (p : Par)
    (hwc : p.wc < 2 ^ W) (hwy : p.wy < 2 ^ W) (v : HS T Q A U) (S : Stacks T A)
    (hborrowed : S.R (rg 0) = binSyms W p.wc) (htarget : S.R (rg 1) = binSyms W p.wy)
    (hblank : ∀ i : Fin 8, i ≠ 0 → i ≠ 1 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 4 * W * (p.wc+p.wy) + 22 * W + 8 * (p.wc+p.wy) + 24 ∧
      Exec body (repairZeroGenerateProgram rg) (mk v S) m
        (mk v' { S with R := repairZeroBank S.R rg p }) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := binaryZeroField_exec body (rg ∘ repairZeroSlot 0)
    (hrg.comp (repairZeroSlot_injective 0)) W p.wc hwc v S hborrowed
    (hblank 4 (by decide) (by decide)) (by intro i; apply hblank <;> fin_cases i <;> decide)
  have hd0 : S.R ((rg ∘ repairZeroSlot 0) .dst) = [] := hblank 2 (by decide) (by decide)
  rw [hd0,List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms p.wc 0) }
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := binaryZeroField_exec body (rg ∘ repairZeroSlot 1)
    (hrg.comp (repairZeroSlot_injective 1)) W p.wy hwy v₁ C
    (by simpa [C,repairZeroSlot,hrg.eq_iff] using htarget)
    (by simp [C,repairZeroSlot,hrg.eq_iff,hblank 4 (by decide) (by decide)]) (by
      intro i
      fin_cases i <;> simp [C,repairZeroSlot,hrg.eq_iff,
        hblank 5 (by decide) (by decide),hblank 6 (by decide) (by decide),hblank 7 (by decide) (by decide)])
  have hd : C.R ((rg ∘ repairZeroSlot 1) .dst) = [] := by
    simp [C,repairZeroSlot,hrg.eq_iff,hblank 3 (by decide) (by decide)]
  rw [hd,List.append_nil] at he₂
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end IntegerMultBounds.MathlibTM2.Routing
