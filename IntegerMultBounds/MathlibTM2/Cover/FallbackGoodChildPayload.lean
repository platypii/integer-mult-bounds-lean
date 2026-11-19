module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildCall

/-! Recover ordinary adapter readiness from the recursive payload result and
preservation of every tape outside the payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm
open FlatCoordinateLayout LabelTraversal
open HeadPivotLayout HeadWidthLayout CrossWeightLayout GoodChildLayout
variable {P U α : Type} {T Q A d r g W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

theorem goodChildPayload_exec (body : P → Pr P T Q A U) (f : P) (host : Fin 58 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (hr : r ≤ d) (g W : ℕ)
    (minor : ∀ j (hj : j < r), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (weight inv : Fin d → ZMod M) (inverse : ∀ j, weight j * inv j = 1)
    (hb : b.Prime) (H : ℕ) (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A)
    (tail rest : List (Fin (A+4))) (budget J : ℕ) (sym : α → Fin 4)
    (source target : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^(d+d)*W) → α)
    (effect : (Fin (M^(d+d)*W) → α) → Prop) :
    let bank := parentWithWeights.trans host
    let machine := parent.trans bank
    let c := child.trans (head.trans (adapterBank.trans machine))
    let s := entry.trans (adapterBank.trans machine)
    let stage := stageAt G r hr minor r le_rfl
    let pivot := fun i : Fin r => stage.M (i.castLE hr) (i.castLE hr)
    let pos := (List.ofFn fun i : Fin r => binSyms H (weight (i.castLE hr) * pivot i).val).flatten
    let reciprocalWords := (List.ofFn fun i : Fin r => binSyms H (inv (i.castLE hr) * Ring.inverse (pivot i)).val).flatten
    let middle := binSyms ((g+g)*H+1) (goodChildDescriptor M r g W).between
    let outputs := [host 55,host 56,host 57]
    let prepared := {S with R := Function.update (Function.update (Function.update S.R (host 55) pos) (host 56) reciprocalWords) (host 57) middle}
    let h := (coeff false).trans (head.trans (adapterBank.trans machine))
    let parentWords := (List.ofFn fun j => binSyms H (weight j).val).flatten ++ rest
    let ready := HeadColumnReady (d := d+d) (W := W) h s H J [] parentWords [] sym source target p q
    ready word S →
    S.R (c 18) = (List.ofFn fun i => binSyms H (pivot i).val).flatten ++ tail →
    S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
    (∀ k : Fin 20, (k ≤ 14 ∧ k ≠ 4) ∨ k = 17 → S.R (c k) = []) →
    (∀ j ∈ outputs, S.R j = []) →
    (∀ u : HS T Q A U, u.user = v.user → ∃ z F n out, z.user = u.user ∧ n ≤ budget ∧
      Exec body (body f) (mk u prepared) n (mk z F) ∧ effect out ∧
      (∀ k, k ≠ s 24 → F.L k = prepared.L k ∧ F.R k = prepared.R k) ∧
      ∀ k, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ out)) k) =
        readAt blank (F.L (s 24)) (F.R (s 24)) (k-p)) →
    ∃ z F n out, z.user = v.user ∧ effect out ∧ ready out F ∧
      (∀ k, k ≠ s 24 → F.L k = S.L k ∧ F.R k = S.R k) ∧
      n ≤ (((List.finRange r).map fun i => childWeightTime b w H i.val).sum+1 + dimensionTime H 1 (g+g)) +
        (budget+2+(2*(r*H+r*H+((g+g)*H+1))+7)) ∧
      Exec body (goodChildCall f host b r g) (mk v S) n (mk z F) := by
  intro bank machine c s stage pivot pos reciprocal middle outputs prepared h parentWords ready initial
    pivots one clock scratch fresh childRun
  let post := fun F : Stacks T A => ∃ out, effect out ∧
    (∀ k, k ≠ s 24 → F.L k = prepared.L k ∧ F.R k = prepared.R k) ∧
    ∀ k, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ out)) k) =
      readAt blank (F.L (s 24)) (F.R (s 24)) (k-p)
  have apart : s 24 ∉ outputs := by
    change host 24 ∉ [host 55,host 56,host 57]
    simp [host.injective.eq_iff]
  obtain ⟨z,F,n,hz,⟨out,act,saved,src⟩,hn,run⟩ := goodChildCall_exec body f host G hr g W minor
    weight inv inverse hb H hm v S tail rest budget post initial.weights pivots initial.modulus one clock scratch
    initial.base initial.one (fun j hj => (initial.scratch j hj).2) fresh (by
      intro u hu
      obtain ⟨z,F,n,out,hz,hn,run,act,saved,src⟩ := childRun u hu
      exact ⟨z,F,n,hz,hn,run,⟨out,act,saved,src⟩,fun j hj => (saved j (fun eq => apart (eq ▸ hj))).2⟩)
  let D := {F with R := fun j => if j ∈ outputs then [] else F.R j}
  have frame (k : Fin T) (ne : k ≠ s 24) : D.L k = S.L k ∧ D.R k = S.R k := by
    refine ⟨(saved k ne).1,?_⟩
    by_cases mem : k ∈ outputs
    · simpa only [D,ite_eq_left mem] using (fresh k mem).symm
    · have miss : k ≠ host 55 ∧ k ≠ host 56 ∧ k ≠ host 57 := by simpa [outputs] using mem
      simpa only [D,ite_eq_right mem,prepared,Function.update_of_ne miss.1,Function.update_of_ne miss.2.1,
        Function.update_of_ne miss.2.2] using (saved k ne).2
  have coeffKeep (j : Fin 17) : D.R (h j) = S.R (h j) :=
    (frame _ (host.injective.ne ((by decide : ∀ j, parentWithWeights (parent (adapterBank (head (coeff false j)))) ≠ 24) j))).2
  have keep (j : Fin 29) (ne : j ≠ 24) := frame (s j) (s.injective.ne ne)
  refine ⟨z,D,n,out,hz,act,?_,frame,hn,run⟩
  refine ⟨(coeffKeep _).trans initial.stage,(coeffKeep _).trans initial.weights,(coeffKeep _).trans initial.reciprocal,
    (coeffKeep _).trans initial.modulus,fun j hj => (coeffKeep _).trans (initial.coeffWork j hj),
    (keep 2 (by decide)).2.trans initial.base,(keep 28 (by decide)).2.trans initial.one,
    (keep 27 (by decide)).2.trans initial.width,?_,?_,?_⟩
  · intro j hj
    have safe := keep j ((by decide : ∀ j ∈ headShearWork, j ≠ 24) j hj)
    exact ⟨safe.1.trans (initial.scratch j hj).1,safe.2.trans (initial.scratch j hj).2⟩
  · simpa only [D,ite_eq_right apart] using src
  · simpa only [(keep 25 (by decide)).1,(keep 25 (by decide)).2] using initial.dst

end IntegerMultBounds.MathlibTM2.Cover.Fallback
