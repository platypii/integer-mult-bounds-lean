module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodTailShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadColumn

/-! Accumulate an archived upper row into its reversed pivot coordinate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout LabelTraversal GoodForm
variable {P U α : Type} {T A d M W : ℕ} [NeZero M]

/-- Read the signed reciprocal, stage and modulus from the shared adapter layout. -/
def tailEntryPorts : Fin 14 ↪ Fin 17 := ⟨![14,1,2,15,3,4,5,6,7,8,9,10,12,13],by decide⟩

def tailRowAt {dim : ℕ} (port : Fin d → Fin dim) (k : Fin d) (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) :
    List (Fin d) → Pr P T 217 A U
  | [] => .act .done
  | i :: rows => .seq (.seq (tailShearAt k i (port i.rev) (port k.rev) (tailEntryPorts.trans coeff) bank)
      (clearWorkTapes (headShearWork.map bank))) (tailRowAt port k coeff bank rows)

noncomputable def tailEntryTimeAt {dim : ℕ} [Fintype P] (body : P → Pr P T 217 A U)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (port : Fin d → Fin dim) (k : Fin d) (M W H J : ℕ) (i : Fin d) : ℕ :=
  let push := max (Fast.Main.mnProgPush (tailShearAt k i (port i.rev) (port k.rev) (tailEntryPorts.trans coeff) bank : Pr P T 217 A U))
    (Fast.Main.mnPushC body)
  4*headShearWork.length+1+(1+6*headShearWork.length*push)*
    ((8*((k.val*d+i.val)*H)+48*H*H+166*H+88)+weightedShearTime (port i.rev) (port k.rev) M W H J)

abbrev tailRowRun (k : Fin d) (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) :
    List (Fin d) → Pr P T 217 A U := tailRowAt id k coeff bank

noncomputable abbrev tailEntryTime [Fintype P] (body : P → Pr P T 217 A U)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (k : Fin d) :=
  tailEntryTimeAt body coeff bank id k

theorem tailRowAt_exec [Fintype P] (body : P → Pr P T 217 A U)
    {dim : ℕ} (port : Fin d → Fin dim) (mono : StrictMono port)
    {β : Type*} (embed : β → (Fin d → ZMod M) → Fin dim → ZMod M)
    (liftShear : ∀ i k (lt : i < k) c u x,
      (RowOp.shear (port i) (port k) (mono lt) c).apply (embed u x) =
        embed u ((RowOp.shear i k lt c).apply x))
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ n (hn : n < rank), IsUnit (lead (n+1) (lt_of_lt_of_le hn hr) G).det)
    (a : Fin rank) (negative : Bool)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (shared : coeff 15 = bank 0)
    (apart : ∀ j : Fin 17, j ≠ 15 → ∀ b, bank b ≠ coeff j)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail parent : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^dim*W : ℕ) → dest z = blank) :
    let k := a.castLE hr
    let stage := (stageAt G rank hr minor a.val a.isLt.le).M
    let childInv := Ring.inverse ((stageAt G rank hr minor rank le_rfl).M k k)
    let c := fun i => let x := elimU k stage (Ring.inverse (stage k k)) i
                      if negative then -x else x
    let ready := HeadColumnReady coeff bank H J (matrixWords A H stage ++ tail)
      parent
      (binSyms H (if negative then -childInv else childInv).val) sym source dest p q (M := M) (d := dim) (W := W)
    let cost := tailEntryTimeAt body coeff bank port k M W H J
    ∀ rows : List (Fin d), (∀ i ∈ rows, k < i) → ∀ v S word, ready word S →
      ∃ z F n out, z.user = v.user ∧ n ≤ (rows.map cost).sum+1 ∧
        Exec body (tailRowAt port k coeff bank rows) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ b, bank b ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ u x j, out (index (embed u ((goodTailRow k c rows).foldl (fun y op => op.apply y) x)) j) =
          word (index (embed u x) j) := by
  intro k stage childInv c ready cost rows
  induction rows with
  | nil =>
    intro _ v S word h
    exact ⟨v,S,1,word,rfl,by simp,Exec.act _ _,h,fun _ _ => ⟨rfl,rfl⟩,fun _ _ _ => rfl⟩
  | cons i rows ih =>
    intro above v S word h
    have lt := above i List.mem_cons_self
    have scratch (j : Fin 29) (hj : j ≤ 26 ∧ j ≠ 2 ∧ j ≠ 24 ∧ j ≠ 25) :=
      h.scratch j (by simpa [headShearWork] using hj)
    obtain ⟨u,D,l,hu,hl,run,frame,base,headers,dst,out,src,effect⟩ :=
      tailShearAt_exec body G rank hr minor a i lt negative (port i.rev) (port k.rev) (mono (Fin.rev_lt_rev.mpr lt)) (tailEntryPorts.trans coeff) bank shared H J hm hw hW
        v S tail h.modulus (fun j hj => h.coeffWork _ ((by decide : ∀ j : Fin 14, j = 1 ∨ 4 ≤ j ∧ j < 12 → tailEntryPorts j ≤ 1 ∨ 3 ≤ tailEntryPorts j ∧ tailEntryPorts j ≤ 11) j hj)) (scratch 0 (by decide)).2 h.base h.one h.width
        (fun j _ hi n2 n24 n25 => (scratch j ⟨hi,n2,n24,n25⟩).2)
        (fun j hj => (h.scratch _ ((by decide : ∀ j : Fin 12, j < 10 → shearTranslation j ∈ headShearWork) j hj)).1)
        sym source dest p q word empty h.src h.dst h.stage h.reciprocal
    obtain ⟨y,E,t,hy,ht,clean,free,keep⟩ := cleanShear_of_exec body _ bank run
      (le_max_left _ (Fast.Main.mnPushC body)) (fun f => (Fast.Main.mn_progPush_le_pushC body f).trans (le_max_right ..)) h.scratch
    have coeffKeep (j : Fin 17) (ne : j ≠ 15) : E.R (coeff j) = S.R (coeff j) := by
      have outside := apart j ne
      exact (keep _ (fun mem => by obtain ⟨x,_,eq⟩ := List.mem_map.mp mem; exact outside x eq)).2.trans (frame _ outside).2
    have bankKeep (j : Fin 29) (hj : j ∉ headShearWork) := keep (bank j)
      (by simpa only [List.mem_map,bank.injective.eq_iff,exists_eq_right] using hj)
    have next : ready out E := by
      refine ⟨(coeffKeep 13 (by decide)).trans h.stage,(coeffKeep 16 (by decide)).trans h.weights,
        (coeffKeep 14 (by decide)).trans h.reciprocal,(coeffKeep 2 (by decide)).trans h.modulus,
        fun j hj => (coeffKeep j (by omega)).trans (h.coeffWork j hj),
        (bankKeep 2 (by decide)).2.trans (base.trans h.base),
        (bankKeep 28 (by decide)).2.trans ((headers 28 (by decide)).trans h.one),
        (bankKeep 27 (by decide)).2.trans ((headers 27 (by decide)).trans h.width),free,?_,?_⟩
      · intro z
        rw [(bankKeep 24 (by decide)).1,(bankKeep 24 (by decide)).2]
        exact (src z).symm
      · intro z
        rw [(bankKeep 25 (by decide)).1,(bankKeep 25 (by decide)).2]
        exact (dst z).symm
    obtain ⟨z,F,n,result,hz,hn,more,done,remainingFrame,act⟩ := ih (fun j hj => above j (List.mem_cons_of_mem _ hj)) y E out next
    refine ⟨z,F,t+n,result,hz.trans (hy.trans hu),?_,Exec.seq clean more,done,?_,?_⟩
    · simp only [List.length_map] at ht
      have step : t ≤ cost i := ht.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _)
      simpa [Nat.add_assoc] using Nat.add_le_add step hn
    · intro j outside
      have saved := keep j (fun mem => by obtain ⟨b,_,eq⟩ := List.mem_map.mp mem; exact outside b eq)
      have endFrame := remainingFrame j outside
      exact ⟨endFrame.1.trans (saved.1.trans (frame j outside).1),
        endFrame.2.trans (saved.2.trans (frame j outside).2)⟩
    · intro u x j
      simpa [goodTailRow,lt] using (act u ((RowOp.shear i.rev k.rev (Fin.rev_lt_rev.mpr lt) (c i)).apply x) j).trans (by rw [← liftShear]; exact effect (embed u x) j)

theorem tailRowRun_exec [Fintype P] (body : P → Pr P T 217 A U)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ n (hn : n < rank), IsUnit (lead (n+1) (lt_of_lt_of_le hn hr) G).det)
    (a : Fin rank) (negative : Bool)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (shared : coeff 15 = bank 0)
    (apart : ∀ j : Fin 17, j ≠ 15 → ∀ b, bank b ≠ coeff j)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail parent : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) :
    let k := a.castLE hr
    let stage := (stageAt G rank hr minor a.val a.isLt.le).M
    let childInv := Ring.inverse ((stageAt G rank hr minor rank le_rfl).M k k)
    let c := fun i => let x := elimU k stage (Ring.inverse (stage k k)) i
                      if negative then -x else x
    let ready := HeadColumnReady coeff bank H J (matrixWords A H stage ++ tail)
      parent
      (binSyms H (if negative then -childInv else childInv).val) sym source dest p q (M := M) (d := d) (W := W)
    let cost := tailEntryTime body coeff bank k M W H J
    ∀ rows : List (Fin d), (∀ i ∈ rows, k < i) → ∀ v S word, ready word S →
      ∃ z F n out, z.user = v.user ∧ n ≤ (rows.map cost).sum+1 ∧
        Exec body (tailRowRun k coeff bank rows) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ b, bank b ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ x j, out (index ((goodTailRow k c rows).foldl (fun y op => op.apply y) x) j) =
          word (index x j) := by
  intro k stage childInv c ready cost rows above v S word initial
  obtain ⟨z,F,n,out,hz,hn,run,done,frame,effect⟩ := tailRowAt_exec body id strictMono_id
    (fun (_ : Unit) x => x) (fun _ _ _ _ _ _ => rfl) G rank hr minor a negative
    coeff bank shared apart H J hm hw hW tail parent sym source dest p q empty rows above v S word initial
  exact ⟨z,F,n,out,hz,hn,run,done,frame,effect ()⟩

theorem fullTailRow_exec [Fintype P] (body : P → Pr P T 217 A U)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ n (hn : n < rank), IsUnit (lead (n+1) (lt_of_lt_of_le hn hr) G).det)
    (a : Fin rank) (negative : Bool)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (shared : coeff 15 = bank 0)
    (apart : ∀ j : Fin 17, j ≠ 15 → ∀ b, bank b ≠ coeff j)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail parent : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+d)*W : ℕ) → dest z = blank) :
    let k := a.castLE hr
    let stage := (stageAt G rank hr minor a.val a.isLt.le).M
    let childInv := Ring.inverse ((stageAt G rank hr minor rank le_rfl).M k k)
    let c := fun i => let x := elimU k stage (Ring.inverse (stage k k)) i
                      if negative then -x else x
    let ready := HeadColumnReady coeff bank H J (matrixWords A H stage ++ tail)
      parent
      (binSyms H (if negative then -childInv else childInv).val) sym source dest p q (M := M) (d := d+d) (W := W)
    let cost := tailEntryTimeAt body coeff bank (Fin.natAdd d) k M W H J
    ∀ rows : List (Fin d), (∀ i ∈ rows, k < i) → ∀ v S word, ready word S →
      ∃ z F n out, z.user = v.user ∧ n ≤ (rows.map cost).sum+1 ∧
        Exec body (tailRowAt (Fin.natAdd d) k coeff bank rows) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ b, bank b ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ x y j, out (index (Fin.append x ((goodTailRow k c rows).foldl (fun y op => op.apply y) y)) j) =
          word (index (Fin.append x y) j) := by
  exact tailRowAt_exec body (Fin.natAdd d) (fun _ _ lt => by simpa using lt) Fin.append
    (fun i k lt c x y => tailShear_append i k lt c x y) G rank hr minor a negative
    coeff bank shared apart H J hm hw hW tail parent sym source dest p q empty

end IntegerMultBounds.MathlibTM2.Cover.Fallback
