module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalWord
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalOuterInput
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStageWidths

/-! The inner router processes one row. Generate its constant row operand and
the shortest borrowed-width operand, preserving the padded source and scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def headerScalarGenerateProgram (rg : Fin 5 → Fin T) : Pr P T Q A U :=
  .seq (.act (Action.push (.rt (rg 1)) (fun _ => bitSymbol true) .done))
    (binaryCanonicalCopyProgram (rg 0) (rg 2) (rg 3) (rg 4))

def headerScalarBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T) (wc : ℕ) :=
  Function.update (Function.update R (rg 1) [bitSymbol true]) (rg 2)
    (binSyms (canonicalScalarWidth wc) wc)

theorem headerScalarGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (W wc : ℕ) (hfit : wc < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms W wc)
    (hblank : ∀ i : Fin 5, i ≠ 0 → S.R (rg i) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (headerScalarGenerateProgram rg) (mk v S) (10 * W + 13)
        (mk v' { S with R := headerScalarBank S.R rg wc }) := by
  let C : Stacks T A := { S with R := Function.update S.R (rg 1) [bitSymbol true] }
  have hp : (Action.push (.rt (rg 1)) (fun _ => bitSymbol true) .done : Act T Q A U).run (mk v S) = mk v C := by
    simp [Action.run,update_rt,C,hblank 1 (by decide)]
  obtain ⟨v',hu,he⟩ := binaryCanonicalWordCopy_exec body (rg 0) (rg 2) (rg 3) (rg 4)
    (by simp [List.nodup_cons,hrg.eq_iff]) W wc hfit v C
    (by simpa [C,hrg.eq_iff] using hsrc)
    (by simp [C,hrg.eq_iff,hblank 2 (by decide)])
    (by simp [C,hrg.eq_iff,hblank 3 (by decide)])
    (by simp [C,hrg.eq_iff,hblank 4 (by decide)])
  have hx := Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) he
  exact ⟨v',hu,Exec.cast hx (by omega) rfl⟩

theorem headerScalarBank_binary (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (wc : ℕ) (i : Fin 2) :
    headerScalarBank R rg wc (rg (if i = 0 then 1 else 2)) =
      canonicalHeaderOperands (canonicalScalarWidth 1) (canonicalScalarWidth wc) 1 wc (.binary i) := by
  fin_cases i <;> simp [headerScalarBank,canonicalHeaderOperands,hrg.eq_iff]
  rfl

end IntegerMultBounds.MathlibTM2.Routing
