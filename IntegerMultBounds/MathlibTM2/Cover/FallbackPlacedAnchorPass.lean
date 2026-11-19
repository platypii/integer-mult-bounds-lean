module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackAnchorPass
public import IntegerMultBounds.MathlibTM2.Host.StatePlacement

/-! Run the sign and anchor pass on the shared host, preserving the residual workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8 ActualAffineScaling RecursiveInterchangeLayout
variable {T n m f b W : ℕ} {P U : Type}
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

theorem placedAnchorPass {K Q : ℕ} (r : Fin 6 ↪ Fin T) (ports : Fin (size n+T) ↪ Fin K)
    (capacity : (anchorProgram n true).1+(anchorProgram n false).1+1 ≤ Q)
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod prime))
    (body : P → Pr P K Q prime U)
    (rs : List (Pair (size n+T))) (hk : rs.length = m*m) (parents saved : Fin (size n+T))
    (layout : (parents :: saved :: (slots rs ++ [port n r 4])).Nodup) :
    ∃ prog, ∀ (v : Descriptor) (w B : ℕ), 0 < w → v.beforeH = B*prime^(m*(w*m)) →
      ∀ (f b W : ℕ), 0 < f → 0 < b → 0 < W → ∀ (a : ℕ → Array n f b W)
      (u : HS K Q prime U) (S : Stacks K prime) (tail : List (Fin (prime+4))),
      let inputs := signedInputs table w (LabelMask.records v) a
      let D := embStk ports S
      Ready n f b W D → ready (prime^(w-1)) D.R rs → D.R saved = [] →
      (D.R parents).length = v.beforeRows*v.rows*B →
      (D.R (port n r 0)).length = (modulus b)^((n+1)*f)*W →
      D.R (port n r 1) = inputs.flatMap (fun a => payloadWord a.2) ++ tail →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), D.R (port n r i) = []) →
      ∃ outs z F t, inputs.Forall₂ Correct outs ∧ Exec body prog (mk u S) t (mk z F) ∧
        t ≤ 1+((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4 +
          ((inputs.map (fun a => cost n T f b W a.1 + 2)).sum + 2) +
          (2*(LabelMask.records v*((modulus b)^((n+1)*f)*W))+2)) ∧
        Ready n f b W (embStk ports F) ∧ z.user = u.user ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L (ports (port n r 1)) = S.L (ports (port n r 1)) ∧
        (∀ j : Fin T, F.R (ports (Fin.natAdd (size n) j)) =
          if j = r 1 then outs.flatMap payloadWord ++ tail else D.R (Fin.natAdd (size n) j)) ∧
        ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨anchor,run⟩ := anchorPass (P := Empty) (U := U) r table Empty.elim rs hk parents saved layout
  have positive : 0 < (anchorProgram n true).1+(anchorProgram n false).1+1 := by omega
  refine ⟨statePlacedNormalized ports capacity positive Empty.elim anchor,?_⟩
  intro v w B hw shape f b W hf hb hW a u S tail inputs D neutral radix free count width queue fresh
  obtain ⟨outs,y,E,t,correct,exec,ht,readyE,hy,hi,ho,left,frame⟩ :=
    run v w B hw shape f b W hf hb hW a (stateLiftDown positive (embDn ports u)) D tail
      neutral radix free count width queue fresh
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized ports ports.injective capacity positive Empty.elim
    (body' := body) (fun e => nomatch e) u S exec
  let F := embOvr ports E.get S
  have eq : embStk ports F = E := embStk_ovr ports.injective _ _
  rw [← eq] at readyE frame left
  exact ⟨outs,z,F,_,correct,placed,Nat.add_le_add_left ht 1,readyE,hz.trans hy,hi,ho,left,frame,
    fun j off => embOvr_off E.get S off⟩

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
