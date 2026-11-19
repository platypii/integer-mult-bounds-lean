module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCrossRead
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadColumn

/-! Execute a mixed cross entry between the two address fields and restore the work tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout LabelTraversal GoodForm Matrix
open M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear
variable {P U α : Type} {T A d M W : ℕ} [NeZero M]

def goodCrossShear (i j : Fin d) (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) : Pr P T 217 A U :=
  .seq (packedHeadCoefficient j.val (i.rev.val*d+j.val) coeff)
    (embProg bank Empty.elim (weightedShear (j.castAdd d) (i.natAdd d) (Function.Embedding.refl _)))

def cleanCrossShear (i j : Fin d) (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) : Pr P T 217 A U :=
  .seq (goodCrossShear i j coeff bank) (clearWorkTapes (headShearWork.map bank))

noncomputable def crossShearTime [Fintype P] (body : P → Pr P T 217 A U)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (i j : Fin d) (M W H J : ℕ) : ℕ :=
  let push := max (Fast.Main.mnProgPush (goodCrossShear i j coeff bank : Pr P T 217 A U)) (Fast.Main.mnPushC body)
  let cost := 8*(j.val*H)+14*H+22+(8*((i.rev.val*d+j.val)*H)+96*H*H+318*H+154)+(2*H+2) +
      weightedShearTime (j.castAdd d) (i.natAdd d) M W H J
  4*headShearWork.length+1+(1+6*headShearWork.length*push)*cost

theorem cleanCrossShear_exec [Fintype P] (body : P → Pr P T 217 A U)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (shared : coeff 15 = bank 0)
    (apart : ∀ t : Fin 17, t ≠ 15 → ∀ b, bank b ≠ coeff t)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ t (ht : t < rank), IsUnit (lead (t+1) (lt_of_lt_of_le ht hr) G).det)
    (idem : G*G = G) (L : Matrix (Fin d) (Fin rank) (ZMod M)) (R : Matrix (Fin rank) (Fin d) (ZMod M))
    (factor : G = L*R) (inv : Fin d → ZMod M) (i j : Fin d)
    (mixed : i.rev.val < rank ↔ ¬ j.val < rank) (negative : Bool)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W) (tail rest : List (Fin (A+4)))
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+d)*W : ℕ) → dest z = blank) :
    let k := if j.val < rank then j else i.rev
    let N := (stageAt G rank hr minor k.val (by dsimp [k]; split <;> omega)).M
    let S := stageAt G rank hr minor rank le_rfl
    let δ := fun t : Fin d => if t.val < rank then S.M t t else 1
    let δ' := fun t : Fin d => if t.val < rank then Ring.inverse (S.M t t) else 1
    let K := kMat (pivotMatrix (revPivots d rank))
      (rev d * S.U * rev d * rev d * (S.L * diagonal δ)) * diagonal (fun t => inv t * δ' t)
    let reciprocal := Ring.inverse (S.M k k)
    let signed := if (if j.val < rank then negative else !negative) then -reciprocal else reciprocal
    let ready := HeadColumnReady coeff bank H J (matrixWords A H N ++ tail)
      ((List.ofFn fun t => binSyms H (inv t).val).flatten ++ rest) (binSyms H signed.val)
      sym source dest p q (M := M) (d := d+d) (W := W)
    ∀ v S word, ready word S → ∃ y E t out, y.user = v.user ∧
      t ≤ crossShearTime body coeff bank i j M W H J ∧
      Exec body (cleanCrossShear i j coeff bank) (mk v S) t (mk y E) ∧ ready out E ∧
      (∀ z, (∀ b, bank b ≠ z) → E.L z = S.L z ∧ E.R z = S.R z) ∧
      ∀ x l, out (index ((crossEntryShear (if negative then -K else K) i j).apply x) l) = word (index x l) := by
  intro k N stage δ δ' K reciprocal signed ready v S word h
  have scratch (t : Fin 29) (ht : t ≤ 26 ∧ t ≠ 2 ∧ t ≠ 24 ∧ t ≠ 25) :=
    h.scratch t (by simpa [headShearWork] using ht)
  obtain ⟨u,l,hu,hl,load⟩ := archivedCross_writes body coeff G rank hr minor idem L R factor inv i j mixed negative
    H hm tail rest v S ⟨h.stage,h.weights,h.reciprocal,h.modulus,h.coeffWork⟩
  rw [shared,(scratch 0 (by decide)).2,List.append_nil] at load
  have lt : j.castAdd d < i.natAdd d := by change j.val < d+i.val; omega
  obtain ⟨z,D,n,hz,hn,run,frame,base,headers,dst,out,src,effect⟩ := loadedShear_exec body _ _ lt
    (if negative then -(K i j) else K i j) bank _ _ H J hm hw hW v S ⟨u,l,hu,hl,load⟩
    h.base h.one h.width (fun t _ hi n2 n24 n25 => (scratch t ⟨hi,n2,n24,n25⟩).2)
    (fun t ht => (h.scratch _ ((by decide : ∀ t : Fin 12, t < 10 → shearTranslation t ∈ headShearWork) t ht)).1)
    sym source dest p q word empty h.src h.dst
  obtain ⟨y,E,t,hy,ht,clean,free,keep⟩ := cleanShear_of_exec body (goodCrossShear i j coeff bank) bank run
    (le_max_left _ (Fast.Main.mnPushC body)) (fun f => (Fast.Main.mn_progPush_le_pushC body f).trans (le_max_right ..)) h.scratch
  have outer (a : Fin T) (outside : ∀ b, bank b ≠ a) : E.L a = S.L a ∧ E.R a = S.R a := by
    have saved := keep a (fun mem => by obtain ⟨b,_,eq⟩ := List.mem_map.mp mem; exact outside b eq)
    exact ⟨saved.1.trans (frame a outside).1,saved.2.trans (frame a outside).2⟩
  have coeffKeep (a : Fin 17) (ne : a ≠ 15) := (outer (coeff a) (apart a ne)).2
  have bankKeep (a : Fin 29) (ha : a ∉ headShearWork) := keep (bank a)
    (by simpa only [List.mem_map,bank.injective.eq_iff,exists_eq_right] using ha)
  refine ⟨y,E,t,out,hy.trans hz,?_,clean,?_,outer,?_⟩
  · simp only [List.length_map] at ht
    exact ht.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hn) _)
  · refine ⟨(coeffKeep 13 (by decide)).trans h.stage,(coeffKeep 16 (by decide)).trans h.weights,
      (coeffKeep 14 (by decide)).trans h.reciprocal,(coeffKeep 2 (by decide)).trans h.modulus,
      fun a ha => (coeffKeep a (by omega)).trans (h.coeffWork a ha),
      (bankKeep 2 (by decide)).2.trans (base.trans h.base),
      (bankKeep 28 (by decide)).2.trans ((headers 28 (by decide)).trans h.one),
      (bankKeep 27 (by decide)).2.trans ((headers 27 (by decide)).trans h.width),free,?_,?_⟩
    · intro pos
      rw [(bankKeep 24 (by decide)).1,(bankKeep 24 (by decide)).2]
      exact (src pos).symm
    · intro pos
      rw [(bankKeep 25 (by decide)).1,(bankKeep 25 (by decide)).2]
      exact (dst pos).symm
  · cases negative <;> exact effect

end IntegerMultBounds.MathlibTM2.Cover.Fallback
