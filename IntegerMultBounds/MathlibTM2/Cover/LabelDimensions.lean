module

public import IntegerMultBounds.MathlibTM2.Cover.LabelSpectators

/-! Prepare the two retained unary loop bounds for the padding pass. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDimensions
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Host Node LabelMask LabelTransport
open RecursiveInterchangeLayout (Descriptor)
variable {T Q A : ℕ} {P U : Type}

/-- Slots 0–6 hold the six caller dimensions and the atom width; 7 and 8 receive the bounds.
The remaining four slots are shared scratch for both computations, with the future payload
slot serving as temporary storage during spectator counting. -/
def program (m : ℕ) (r : Fin 13 ↪ Fin T) : Pr P T Q A U :=
  .seq (LabelSpectators.program m (r 0) (r 1) (r 2) (r 6) (r 8) (r 7) (r 9) (r 10))
    (LabelPayload.program (r 4) (r 5) (r 3) (r 9) (r 8) (r 10) (r 11) (r 12))

def inputs (r : Fin 13 ↪ Fin T) (R : Regs T A) (v : Descriptor) (w : ℕ) :=
  (R (r 0)).length = v.beforeRows ∧ (R (r 1)).length = v.rows ∧
  (R (r 2)).length = v.beforeH ∧ (R (r 3)).length = v.width ∧
  (R (r 4)).length = v.between ∧ (R (r 5)).length = v.afterD ∧ (R (r 6)).length = w

theorem runs (body : P → Pr P T Q A U) (r : Fin 13 ↪ Fin T) (m w B : ℕ) (hm : 0 < m)
    (v : Descriptor) (hp : v.Positive) (hv : v.beforeH = B*prime^(m*(w*m)))
    (u : HS T Q A U) (S : Stacks T A) (hin : inputs r S.R v w)
    (hf : ∀ i : Fin 13, 7 ≤ i.val → S.R (r i) = []) :
    let R := Function.update S.R (r 7) (List.replicate (v.beforeRows*v.rows*B) tick)
    ∃ z c, z.user = u.user ∧ c ≤ 44*records v + 13*w + 37*payload v + 20 ∧
      Exec body (program m r) (mk u S) c
        (mk z {S with R := Function.update R (r 8) (List.replicate (payload v) tick)}) := by
  obtain ⟨ha,hb,hh,hw,hmid,hend,hatom⟩ := hin
  obtain ⟨u₁,c₁,hu₁,hc₁,he₁⟩ := LabelSpectators.runs body m hm
    (r 0) (r 1) (r 2) (r 6) (r 8) (r 7) (r 9) (r 10) (by simp)
    v hp w B hv u S ha hb hh hatom (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact hf _ (by decide))
  let M : Stacks T A := {S with R := Function.update S.R (r 7) (List.replicate (v.beforeRows*v.rows*B) tick)}
  have same (i : Fin 13) (hi : i ≠ 7) : M.R (r i) = S.R (r i) :=
    Function.update_of_ne (fun h => hi (r.injective h)) ..
  obtain ⟨z,c₂,hu₂,hc₂,he₂⟩ := LabelPayload.runs body (r 4) (r 5) (r 3) (r 9) (r 8)
    (r 10) (r 11) (r 12) (by simp) v hp u₁ M
    ((congrArg List.length (same 4 (by decide))).trans hmid)
    ((congrArg List.length (same 5 (by decide))).trans hend)
    ((congrArg List.length (same 3 (by decide))).trans hw) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        exact (same _ (by decide)).trans (hf _ (by decide)))
  exact ⟨z,c₁+c₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂⟩

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDimensions
