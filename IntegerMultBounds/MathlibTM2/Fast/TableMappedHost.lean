module

public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! Publish table emissions through a symbol map, preserving the table and external frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {n : ℕ}
  {rg : TblR n → Fin T}

def tblMapHost (rg : TblR n → Fin T) (c : TblCode n) (out : Fin T) (f : Fin (A+4) → Fin (A+4)) : Pr P T Q A U :=
  .seq (tblCompile rg c) (moveR (rg .acc) out f)

/-- **Streams on the host.** A program that terminates from `st` (with `acc` empty) within `K`
atoms in a state `st'` satisfying `Post` runs as `tblMapHost` in at most
`K · tblC W w + 2 |st'.acc| + 2` steps; the output register `out` (outside the layout) gains the
symbols of `acc` in emission order, `st'.acc.reverse`, on top; the layout carries `st'` with
`acc` emptied; every other register and the input, output and left stacks are unchanged. -/
theorem tblMapHost_runs (f : Fin (A+4) → Fin (A+4)) (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) {c : TblCode n} {st : TblSt n A} {Post : TblSt n A → Prop} {K : ℕ}
    (h : TblDo A W w c st Post K) (hst : ∀ j, st.val j < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m st', Post st' ∧ v'.user = v.user ∧ m ≤ K * tblC W w + 2 * st'.acc.length + 2 ∧
      Exec body (tblMapHost rg c out f) (mk v S) m (mk v' S') ∧
      S'.R out = (st'.acc.map f).reverse ++ S.R out ∧
      tblHolds rg S' (tblRho W wl nl ⟨st'.val, []⟩) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.L = S.L ∧ ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨st', hp, hr⟩ := TblDo.host (body := body) hrg wl nl hwl hnl hw h hst
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := hr v S hS
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (rg .acc) out (hout .acc) f v₁ S₁
  have hacc₁ : S₁.R (rg .acc) = st'.acc := hS₁ .acc
  refine ⟨v₂, _, _, st', hp, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, ?_, hf₁.1, hf₁.2.1,
    hf₁.2.2.1, fun k hk1 hk2 => ?_⟩
  · rw [hacc₁]; omega
  · simp only [movedR, Function.update_self, hacc₁]
    rw [hf₁.2.2.2 out hout]
  · intro r
    simp only [movedR]
    rw [Function.update_of_ne (hout r)]
    by_cases hr : r = .acc
    · subst hr; simp [tblRho]
    · rw [Function.update_of_ne (hrg.ne hr), hS₁ r]
      cases r <;> simp_all [tblRho]
  · simp only [movedR]
    rw [Function.update_of_ne hk1, Function.update_of_ne (Ne.symm (hk2 .acc)), hf₁.2.2.2 k hk2]


end IntegerMultBounds.MathlibTM2.Fast.TableVM
