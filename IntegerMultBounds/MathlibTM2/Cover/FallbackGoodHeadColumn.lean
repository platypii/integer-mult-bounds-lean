module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadShear

/-! Run a pivot column while keeping the stage archive and signed reciprocal fixed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout LabelTraversal GoodForm
variable {P U α : Type} {T A d M W : ℕ} [NeZero M]

def headColumnRun (k : Fin d) (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) :
    List (Fin d) → Pr P T 217 A U
  | [] => .act .done
  | i :: rows => .seq (cleanGoodHeadShear k i coeff bank) (headColumnRun k coeff bank rows)

/-- Between rows the modulus, width, stage matrix and signed weight are ready
for another coefficient lookup. Both payload heads retain their logical origins. -/
structure HeadColumnReady (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T)
    (H J : ℕ) (matrix parent pivot : List (Fin (A+4))) (sym : α → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α) (S : Stacks T A) : Prop where
  stage : S.R (coeff 13) = matrix
  weights : S.R (coeff 16) = parent
  reciprocal : S.R (coeff 14) = pivot
  modulus : S.R (coeff 2) = binSyms H M
  coeffWork : ∀ j : Fin 17, j ≤ 1 ∨ 3 ≤ j ∧ j ≤ 11 → S.R (coeff j) = []
  base : S.R (bank 2) = binSyms H M
  one : S.R (bank 28) = binSyms 1 1
  width : S.R (bank 27) = binSyms J W
  scratch : ∀ j ∈ headShearWork, S.L (bank j) = [] ∧ S.R (bank j) = []
  src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ word)) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p)
  dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)

theorem headColumnRun_exec [Fintype P] (body : P → Pr P T 217 A U)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ n (hn : n < rank), IsUnit (lead (n+1) (lt_of_lt_of_le hn hr) G).det)
    (a : Fin rank) (weights inv : Fin d → ZMod M) (negative : Bool)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (shared : coeff 15 = bank 0)
    (apart : ∀ j : Fin 17, j ≠ 15 → ∀ b, bank b ≠ coeff j)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail rest : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) :
    let k := a.castLE hr
    let stage := (stageAt G rank hr minor a.val a.isLt.le).M
    let childInv := inv k * Ring.inverse ((stageAt G rank hr minor rank le_rfl).M k k)
    let c := fun i => let x := weights i * (stage i k * Ring.inverse (stage k k)) * inv k
                      if negative then -x else x
    let ready := HeadColumnReady coeff bank H J (matrixWords A H stage ++ tail)
      ((List.ofFn fun j => binSyms H (weights j).val).flatten ++ rest)
      (binSyms H (if negative then -childInv else childInv).val) sym source dest p q (M := M) (d := d) (W := W)
    let cost := fun (i : Fin d) =>
      let push := max (Fast.Main.mnProgPush (goodHeadShear k i coeff bank : Pr P T 217 A U)) (Fast.Main.mnPushC body)
      4*headShearWork.length+1+(1+6*headShearWork.length*push)*
        ((8*(i.val*H)+14*H+22+(8*((i.val*d+k.val)*H)+96*H*H+318*H+154)+(2*H+2)) +
          weightedShearTime k i M W H J)
    ∀ rows : List (Fin d), (∀ i ∈ rows, k < i) → ∀ v S word, ready word S →
      ∃ z F n out, z.user = v.user ∧ n ≤ (rows.map cost).sum+1 ∧
        Exec body (headColumnRun k coeff bank rows) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ b, bank b ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ x j, out (index ((rows.flatMap fun i => addWord k i (c i)).foldl (fun y op => op.apply y) x) j) =
          word (index x j) := by
  intro k stage childInv c ready cost rows
  induction rows with
  | nil =>
    intro _ v S word h
    exact ⟨v,S,1,word,rfl,by simp,Exec.act _ _,h,fun _ _ => ⟨rfl,rfl⟩,fun _ _ => rfl⟩
  | cons i rows ih =>
    intro above v S word h
    have lt := above i List.mem_cons_self
    have scratch (j : Fin 29) (hj : j ≤ 26 ∧ j ≠ 2 ∧ j ≠ 24 ∧ j ≠ 25) :=
      h.scratch j (by simpa [headShearWork] using hj)
    obtain ⟨u,D,l,hu,hl,run,frame,base,headers,dst,out,src,effect⟩ :=
      goodHeadShear_exec body G rank hr minor a i lt weights inv negative coeff bank shared H J hm hw hW
        v S tail rest h.modulus h.coeffWork (scratch 0 (by decide)).2 h.base h.one h.width
        (fun j _ hi n2 n24 n25 => (scratch j ⟨hi,n2,n24,n25⟩).2)
        (fun j hj => (h.scratch _ ((by decide : ∀ j : Fin 12, j < 10 → shearTranslation j ∈ headShearWork) j hj)).1)
        sym source dest p q word empty h.src h.dst h.stage h.weights h.reciprocal
    obtain ⟨y,E,t,hy,ht,clean,free,keep⟩ := cleanGoodHeadShear_of_exec body k i coeff bank run
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
    · intro x j
      simpa [addWord,lt] using (act ((RowOp.shear k i lt (c i)).apply x) j).trans (effect x j)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
