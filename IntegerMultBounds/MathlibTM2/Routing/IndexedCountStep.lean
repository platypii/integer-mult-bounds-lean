module

public import IntegerMultBounds.MathlibTM2.Routing.IndexedCountLoop
public import IntegerMultBounds.MathlibTM2.Routing.WordRepeatStep

/-! A counted residue round runs a framed call, increments its live binary index,
and archives one count symbol. The arithmetic temporary restores each round. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def indexedCountStepProgram (count saved index tmp cy : Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq call (.seq (countIter index tmp cy) (.act (wordRepeatArchive count saved)))

def indexedCountStepBank (R : Fin T → List (Fin (A + 4))) (count saved index dst : Fin T)
    (L i : ℕ) (c : Fin (A + 4)) (rest output : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update R dst output)
    index (binSyms L (i + 1))) count rest) saved (c :: R saved)

theorem indexedCountStep_exec (body : P → Pr P T Q A U)
    (count saved index dst tmp cy : Fin T) (hreg : [count,saved,index,dst,tmp].Nodup)
    (L i : ℕ) (c : Fin (A + 4)) (rest output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = c :: rest) (hindex : S.R index = binSyms L i) (htmp : S.R tmp = [])
    (hcall : ∀ u : HS T Q A U, ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
      Exec body call (mk u S) m (mk u' { S with R := Function.update S.R dst output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ price + 4 * L + 6 ∧
      Exec body (indexedCountStepProgram count saved index tmp cy call) (mk v S) m
        (mk v' { S with R := indexedCountStepBank S.R count saved index dst L i c rest output }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := hcall v
  let C : Stacks T A := { S with R := Function.update S.R dst output }
  obtain ⟨v₂, hu₂, hex₂⟩ := countIter_exec (body := body) (c := index) (tmp := tmp) ‹index ≠ tmp› cy v₁ C
    (by simpa [C, ‹index ≠ dst›] using hindex)
    (by simpa [C, (Ne.symm ‹dst ≠ tmp›)] using htmp)
  let D : Stacks T A := { C with R := Function.update C.R index (binSyms L (i + 1)) }
  let v₃ := { v₂ with sym := some c }
  let E : Stacks T A := { D with R := Function.update (Function.update D.R count rest) saved (c :: D.R saved) }
  have hdcount : D.R count = c :: rest := by
    simpa [D, C, ‹count ≠ index›, ‹count ≠ dst›] using hcount
  have hp : (wordRepeatArchive count saved : Act T Q A U).run (mk v₂ D) = mk v₃ E := by
    simp [wordRepeatArchive, Action.run, update_rt, hdcount, v₃, E, (Ne.symm ‹count ≠ saved›)]
  have hf : E.R = indexedCountStepBank S.R count saved index dst L i c rest output := by
    simp [E, D, C, indexedCountStepBank, ‹saved ≠ index›,
      ‹saved ≠ dst›]
  refine ⟨v₃, m₁ + ((4 * L + 5) + 1), hu₂.trans hu₁, by omega, ?_⟩
  have hex := Exec.seq hex₁ (Exec.seq hex₂ (hp ▸ Exec.act (body := body) _ (mk v₂ D)))
  exact hex.cast rfl (by rw [show E = { S with R := E.R } from rfl, hf])

end IntegerMultBounds.MathlibTM2.Routing
