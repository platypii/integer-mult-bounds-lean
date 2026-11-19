module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairWeights
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove

/-! Pack the rank child's diagonal and its reciprocal from the parent and pivot archives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {P U : Type} {T Q A d r b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def childWeightStep (b i : ℕ) (bank : Fin 22 ↪ Fin T) : Pr P T Q A U :=
  .seq (packedChildPair b i i ((Fin.castLEEmb (by decide)).trans bank))
    (.seq (moveRightOrdered (bank 14) (bank 1) (bank 20)) (moveRightOrdered (bank 0) (bank 1) (bank 21)))

def childWeightTime (b w H i : ℕ) :=
  let C := 48*H*H+152*H+66
  (8*(i*H)+14*H+22) + ((8*(i*H)+48*H*H+166*H+88)+(6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C)))) +
    (2*H+2) + ((4*H+4)+(4*H+4))

theorem childWeightStep_exec (body : P → Pr P T Q A U) (bank : Fin 22 ↪ Fin T)
    (weight inv : Fin d → ZMod M) (pivot : Fin r → ZMod M) (hr : r ≤ d) (i : Fin r)
    (inverse : ∀ j, weight j * inv j = 1) (unit : IsUnit (pivot i)) (hb : b.Prime)
    (H : ℕ) (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail rest : List (Fin (A+4)))
    (weights : S.R (bank 19) = (List.ofFn fun k => binSyms H (weight k).val).flatten ++ rest)
    (record : S.R (bank 18) = (List.ofFn fun k => binSyms H (pivot k).val).flatten ++ tail)
    (modulus : S.R (bank 4) = binSyms H M) (one : S.R (bank 15) = binSyms H (1 : ZMod M).val)
    (clock : (S.R (bank 16)).length = w)
    (free : ∀ k : Fin 20, (k ≤ 14 ∧ k ≠ 4) ∨ k = 17 → S.R (bank (k.castLE (by decide))) = []) :
    let pos := binSyms H (weight (i.castLE hr) * pivot i).val
    let reciprocal := binSyms H (inv (i.castLE hr) * Ring.inverse (pivot i)).val
    ∃ z t, z.user = v.user ∧ t ≤ childWeightTime b w H i.val ∧
      Exec body (childWeightStep b i.val bank) (mk v S) t (mk z {S with R := Function.update (Function.update S.R (bank 20) (pos ++ S.R (bank 20))) (bank 21) (reciprocal ++ S.R (bank 21))}) := by
  intro pos reciprocal
  let c := (Fin.castLEEmb (by decide : 20 ≤ 22)).trans bank
  obtain ⟨u,D,l,hu,hl,run,prod,invWord,left,inp,out,frame⟩ := packedChildPair_exec body c weight (i.castLE hr)
    (inv (i.castLE hr)) (inverse _) pivot i unit hb H hm v S tail rest weights record modulus one clock free
  change D.R (bank 14) = pos at prod
  change D.R (bank 0) = reciprocal at invWord
  have keep (k : Fin 22) (h0 : k ≠ 0) (h14 : k ≠ 14) := frame (bank k) (bank.injective.ne h0) (bank.injective.ne h14)
  have blank : D.R (bank 1) = [] := (keep 1 (by decide) (by decide)).trans (free 1 (by decide))
  obtain ⟨y,hy,push⟩ := moveRightOrdered_exec (body := body) (bank 14) (bank 1) (bank 20)
    (bank.injective.ne (by decide)) (bank.injective.ne (by decide)) (bank.injective.ne (by decide)) u D blank
  let E := {D with R := Function.update (Function.update D.R (bank 14) []) (bank 20) (pos ++ S.R (bank 20))}
  rw [prod,keep 20 (by decide) (by decide)] at push
  have same (k : Fin 22) (h14 : k ≠ 14) (h20 : k ≠ 20) : E.R (bank k) = D.R (bank k) := by
    simp [E,Function.update_of_ne,bank.injective.ne h14,bank.injective.ne h20]
  obtain ⟨z,hz,pushInv⟩ := moveRightOrdered_exec (body := body) (bank 0) (bank 1) (bank 21)
    (bank.injective.ne (by decide)) (bank.injective.ne (by decide)) (bank.injective.ne (by decide)) y E
    ((same 1 (by decide) (by decide)).trans blank)
  rw [same 0 (by decide) (by decide),invWord,same 21 (by decide) (by decide),keep 21 (by decide) (by decide)] at pushInv
  refine ⟨z,_,hz.trans (hy.trans hu),?_,(Exec.seq run (Exec.seq push pushInv)).cast rfl ?_⟩
  · simpa only [pos,reciprocal,length_binSyms,Fin.val_castLE,childWeightTime] using Nat.add_le_add_right hl ((4*H+4)+(4*H+4))
  · apply congrArg (mk z)
    refine Stacks.ext inp out left ?_
    funext k
    have blank0 : S.R (bank 0) = [] := free 0 (by decide)
    have blank14 : S.R (bank 14) = [] := free 14 (by decide)
    by_cases h21 : k = bank 21
    · simp [h21]
    by_cases h20 : k = bank 20
    · simp [h20,E]
    by_cases h0 : k = bank 0
    · simp [h0,blank0]
    by_cases h14 : k = bank 14
    · simp [E,h14,blank14]
    simpa only [E,Function.update_of_ne h21,Function.update_of_ne h20,Function.update_of_ne h0,
      Function.update_of_ne h14] using frame k h0 h14

def childWeightList (b : ℕ) (bank : Fin 22 ↪ Fin T) : List (Fin r) → Pr P T Q A U
  | [] => .act .done
  | i :: rows => .seq (childWeightList b bank rows) (childWeightStep b i.val bank)

theorem childWeightList_exec (body : P → Pr P T Q A U) (bank : Fin 22 ↪ Fin T)
    (weight inv : Fin d → ZMod M) (pivot : Fin r → ZMod M) (hr : r ≤ d) (rows : List (Fin r))
    (inverse : ∀ j, weight j * inv j = 1) (unit : ∀ i, IsUnit (pivot i)) (hb : b.Prime)
    (H : ℕ) (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail rest : List (Fin (A+4)))
    (weights : S.R (bank 19) = (List.ofFn fun k => binSyms H (weight k).val).flatten ++ rest)
    (record : S.R (bank 18) = (List.ofFn fun k => binSyms H (pivot k).val).flatten ++ tail)
    (modulus : S.R (bank 4) = binSyms H M) (one : S.R (bank 15) = binSyms H (1 : ZMod M).val)
    (clock : (S.R (bank 16)).length = w)
    (free : ∀ k : Fin 20, (k ≤ 14 ∧ k ≠ 4) ∨ k = 17 → S.R (bank (k.castLE (by decide))) = []) :
    let pos := fun i : Fin r => binSyms H (weight (i.castLE hr) * pivot i).val
    let reciprocal := fun i : Fin r => binSyms H (inv (i.castLE hr) * Ring.inverse (pivot i)).val
    ∃ z t, z.user = v.user ∧ t ≤ (rows.map (fun i => childWeightTime b w H i.val)).sum+1 ∧
      Exec body (childWeightList b bank rows) (mk v S) t
        (mk z {S with R := Function.update (Function.update S.R (bank 20) (rows.flatMap pos ++ S.R (bank 20))) (bank 21) (rows.flatMap reciprocal ++ S.R (bank 21))}) := by
  intro pos reciprocal
  induction rows with
  | nil =>
    refine ⟨v,1,rfl,by simp,?_⟩
    simpa [childWeightList,Function.update_of_ne (bank.injective.ne (by decide : (21 : Fin 22) ≠ 20)),
      Function.update_eq_self] using Exec.act (body := body) (.done) (mk v S)
  | cons i rows ih =>
    obtain ⟨u,l,hu,hl,run⟩ := ih
    let D := {S with R := Function.update (Function.update S.R (bank 20) (rows.flatMap pos ++ S.R (bank 20))) (bank 21) (rows.flatMap reciprocal ++ S.R (bank 21))}
    have keep (k : Fin 22) (hk : k < 20) : D.R (bank k) = S.R (bank k) := by
      simp [D,Function.update_of_ne (bank.injective.ne (by omega : k ≠ 20)),
        Function.update_of_ne (bank.injective.ne (by omega : k ≠ 21))]
    obtain ⟨z,t,hz,ht,step⟩ := childWeightStep_exec body bank weight inv pivot hr i inverse (unit i) hb H hm
      u D tail rest ((keep 19 (by decide)).trans weights) ((keep 18 (by decide)).trans record)
      ((keep 4 (by decide)).trans modulus) ((keep 15 (by decide)).trans one)
      ((congrArg List.length (keep 16 (by decide))).trans clock)
      (fun k hk => (keep _ k.isLt).trans (free k hk))
    refine ⟨z,l+t,hz.trans hu,?_,(Exec.seq run step).cast rfl ?_⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · apply congrArg (mk z)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases h21 : k = bank 21 <;> by_cases h20 : k = bank 20 <;>
        simp [D,h21,h20,bank.injective.eq_iff,List.append_assoc,pos,reciprocal]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
