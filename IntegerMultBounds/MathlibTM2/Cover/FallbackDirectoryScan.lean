module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryAdvance
public import IntegerMultBounds.MathlibTM2.Cover.FallbackMaskedScan

/-! Consume the directory in physical order and collect one output per mask bit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q : ℕ} {P U : Type}

theorem directoryScan_exec (body : P → Pr P T Q prime U) (r : Fin 6 ↪ Fin T) (mask : Fin T)
    (outside : ∀ k, mask ≠ r k) (m w records : ℕ) (active : ℕ → Bool)
    (live padding : Pr P T Q prime U) (cost : ℕ → ℕ)
    (ancestor word : ℕ → List (Fin (prime+4))) (tail acc : List (Fin (prime+4)))
    (workspace : Regs T prime → Prop)
    (stable : ∀ R M, workspace R → (∀ k, k ≠ mask → k ≠ r 2 → k ≠ r 5 → M k = R k) → workspace M)
    (emit : ∀ j < records, Writes body (fun R => workspace R ∧
      ∃ rest, R (r 2) = LabelDirectory.entry ancestor m w j ++ rest) (r 4)
      (if active j then live else padding) (word j) (cost j))
    (v : HS T Q prime U) (S : Stacks T prime) (start : workspace S.R)
    (widths : ∀ j < records, (S.R (r 0)).length = (ancestor j).length)
    (width : (S.R (r 1)).length = w) (blank : S.R (r 3) = []) (empty : S.R (r 4) = [])
    (directory : S.R (r 2) = (List.range records).flatMap (LabelDirectory.entry ancestor m w) ++ tail)
    (output : S.R (r 5) = acc) (bits : S.R mask = (List.range records).map fun j => bitSymbol (active j)) :
    let branch := fun p => Prog.seq p (.seq (moveR (r 4) (r 5) id) (advanceDirectory m r))
    ∃ z F n, z.user = v.user ∧ F.R mask = [] ∧ F.R (r 2) = tail ∧
      F.R (r 5) = ((List.range records).flatMap word).reverse ++ acc ∧
      (∀ k, k ≠ mask → k ≠ r 2 → k ≠ r 5 → F.R k = S.R k) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      n ≤ ((List.range records).map fun j => cost j+2*(word j).length+2+
        (4*(ancestor j).length+4+(m*m*(4*w+4)+1))+4).sum+2 ∧
      Exec body (maskedScan mask (branch live) (branch padding)) (mk v S) n (mk z F) := by
  intro branch
  let entries := LabelDirectory.entry ancestor m w
  let remaining := fun j => ((List.range records).drop j).flatMap entries ++ tail
  let collected := fun j => ((List.range j).flatMap word).reverse ++ acc
  let inv := fun j (B : Stacks T prime) => B.R (r 2) = remaining j ∧ B.R (r 5) = collected j ∧
    (∀ k, k ≠ mask → k ≠ r 2 → k ≠ r 5 → B.R k = S.R k) ∧ B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L
  have release (j) (B : Stacks T prime) xs (h : inv j B) : inv j {B with R := Function.update B.R mask xs} :=
    ⟨(Function.update_of_ne (outside 2).symm _ _).trans h.1,(Function.update_of_ne (outside 5).symm _ _).trans h.2.1,
      fun k hm hd ha => (Function.update_of_ne hm _ _).trans (h.2.2.1 k hm hd ha),h.2.2.2⟩
  apply Exists.elim (maskedRange_exec body mask (branch live) (branch padding) records active _ inv release ?_ v S
    ⟨by simpa [remaining,entries] using directory,by simpa [collected] using output,fun _ _ _ _ => rfl,rfl,rfl,rfl⟩ bits)
  · rintro z ⟨F,n,hz,h,clear,hn,run⟩
    exact ⟨z,F,n,hz,clear,by simpa [remaining,List.drop_of_length_le (show (List.range records).length ≤ records by simp)] using h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2,hn,run⟩
  · intro j hj u B h
    have atHead : remaining j = entries j ++ remaining (j+1) := by
      have split := List.getElem_cons_drop (show j < (List.range records).length by simpa)
      simp only [List.getElem_range] at split
      simp only [remaining,← split,List.flatMap_cons,List.append_assoc]
    have dir := h.1.trans atHead
    have get (i : Fin 6) (hd : i ≠ 2) (ha : i ≠ 5) := h.2.2.1 (r i) (outside i).symm (r.injective.ne hd) (r.injective.ne ha)
    obtain ⟨z,n,hz,hn,run⟩ := collectDirectory_exec body r m w j _ _ _ (ancestor j) (remaining (j+1)) _ (emit j hj)
      u B ⟨stable _ _ start h.2.2.1,_,dir⟩ ((get 4 (by decide) (by decide)).trans empty)
      (by simpa [entries,LabelDirectory.entry,List.append_assoc] using dir)
      ((congrArg List.length (get 0 (by decide) (by decide))).trans (widths j hj))
      ((congrArg List.length (get 1 (by decide) (by decide))).trans width) ((get 3 (by decide) (by decide)).trans blank)
    refine ⟨z,{B with R := Function.update (Function.update B.R (r 5) ((word j).reverse ++ B.R (r 5))) (r 2) (remaining (j+1))},n,hz,⟨Function.update_self ..,?_,?_,h.2.2.2⟩,?_,hn,?_⟩
    · simp [collected,List.range_succ,List.reverse_append,List.append_assoc,h.2.1]
    · intro k hm hd ha
      simpa [Function.update_of_ne hd,Function.update_of_ne ha] using h.2.2.1 k hm hd ha
    · simp [Function.update_of_ne (outside _)]
    · cases eq : active j <;> simpa [branch,eq] using run

end IntegerMultBounds.MathlibTM2.Cover.Fallback
