module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectorySetup
public import IntegerMultBounds.MathlibTM2.Cover.LabelSpectators

/-! One residue traversal supplies both the directory record count and its branch mask. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryClasses
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Host Node LabelTraversal RecursiveInterchangeLayout

variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q prime U}

/-- Traverse the physical labels, retain their class bits, and build the matching directory. -/
theorem realizes (m : ℕ) (hm : 0 < m) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool)
    (r : Fin 15 ↪ Fin T) (atom one : Fin T) (ha : ∀ i, atom ≠ r i) (ho : ∀ i, one ≠ r i)
    (rs : List (Pair T)) (hk : rs.length = m*m)
    (hr : (r 9 :: r 13 :: (slots rs ++ [r 12])).Nodup) :
    ∃ p : Pr P T Q prime U, ∀ (v : Descriptor) (w D : ℕ), 0 < w →
      v.beforeH = D*prime^(m*(w*m)) → ∀ (word : ℕ → List (Fin (prime+4)))
      (tail : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime),
      (S.R atom).length = w → (S.R one).length = 1 → ready (prime^(w-1)) S.R rs →
      let N := v.beforeRows*v.rows*D
      let L := w*(m*m)
      let B := prime^L
      let W := (S.R (r 1)).length
      let ids := List.range (N*B)
      let keep := fun k => branch (LabelStock.residue m w 1 k)
      let R := Function.update S.R (r 12) ((ids.map keep).map bitSymbol)
      (S.R (r 9)).length = N → S.R (r 0) = (List.range N).flatMap word ++ tail →
      (∀ i < N, (word i).length = W) →
      (∀ i ∈ ([2,3,4,5,6,7,10,11,12,13] : List (Fin 15)), S.R (r i) = []) →
      ∃ z n, z.user = u.user ∧ n ≤ N*(time (prime^(w-1)) (m*m) 1+5)+4 +
        (8*w+8+22*B + (N*B*(9*L+15)+6+(N*(B*(8*W+11)+6*W+15)+6+N*B*(6*(W+L)+13)+6))) ∧
        Exec body p (mk u S) n (mk z {S with R := Function.update (Function.update
          (LabelDirectorySetup.prepared R r L) (r 0) tail) (r 14) (ids.flatMap
          (LabelDirectory.entry (fun k => word (k/B)) m w) ++ S.R (r 14))}) := by
  obtain ⟨gen,hgen⟩ := class_writes (body := body) m branch rs hk (r 12) (r 9) (r 13) hr
  refine ⟨.seq gen (.seq (LabelDirectorySetup.setup m r atom one) (LabelDirectoryBuild.program r)),?_⟩
  intro v w D hw hv word tail u S atomWidth unit ready N L B W ids keep R count source width fresh
  have records : LabelMask.records v = N*B := by
    unfold LabelMask.records N B L
    rw [hv, Nat.mul_assoc (v.beforeRows*v.rows)]
    congr 3
    ring
  obtain ⟨u',n,hu,hn,he⟩ := hgen v w D hw hv u S ⟨ready,fresh 13 (by simp),count⟩
  rw [records,fresh 12 (by simp),List.append_nil] at he
  let M : Stacks T prime := {S with R := R}
  have ma : (M.R atom).length = w := by simpa [M,R,ha] using atomWidth
  have parents : (M.R (r 9)).length = N := by simpa [M,R] using count
  have prefixWidth : (M.R (r 1)).length = W := by simp [M,R,W]
  obtain ⟨z,t,hz,ht,run⟩ := LabelDirectorySetup.build_from_mask (body := body) m r atom one ha ho u' M
    word tail keep (by simpa [M,R,ho] using unit) (by
      intro i hi
      have ne : i ≠ 12 := by rintro rfl; simp at hi
      simp only [M,R,Function.update_of_ne (r.injective.ne ne)]
      apply fresh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rw [ma]; exact Nat.mul_pos hw (Nat.mul_pos hm hm))
    (by rw [parents,ma]; simp [M,R,ids,B,L]) (by rw [parents]; simpa [M,R] using source)
    (by rw [parents,prefixWidth]; exact width)
  rw [ma,parents,prefixWidth] at ht
  refine ⟨z,n+t,hz.trans hu,Nat.add_le_add hn ht,?_⟩
  simpa only [ma,parents,M,R,Function.update_of_ne (r.injective.ne (by decide : (14 : Fin 15) ≠ 12))]
    using Exec.seq he run

/-- Derive the common parent count from the physical descriptor before traversing the labels. -/
theorem from_dimensions (m : ℕ) (hm : 0 < m) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool)
    (r : Fin 15 ↪ Fin T) (atom one : Fin T) (ha : ∀ i, atom ≠ r i) (ho : ∀ i, one ≠ r i)
    (beforeRows rows beforeH : Fin T)
    (layout : [beforeRows,rows,beforeH,atom,r 2,r 9,r 3,r 5].Nodup)
    (rs : List (Pair T)) (hk : rs.length = m*m)
    (hr : (r 9 :: r 13 :: (slots rs ++ [r 12])).Nodup) :
    ∃ p : Pr P T Q prime U, ∀ (v : Descriptor) (w D : ℕ), 0 < w → v.Positive →
      v.beforeH = D*prime^(m*(w*m)) → ∀ (word : ℕ → List (Fin (prime+4)))
      (tail : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime),
      (S.R beforeRows).length = v.beforeRows → (S.R rows).length = v.rows →
      (S.R beforeH).length = v.beforeH → (S.R atom).length = w → (S.R one).length = 1 → ready (prime^(w-1)) S.R rs →
      let N := v.beforeRows*v.rows*D
      let L := w*(m*m)
      let B := prime^L
      let W := (S.R (r 1)).length
      let ids := List.range (N*B)
      let keep := fun k => branch (LabelStock.residue m w 1 k)
      let C := Function.update S.R (r 9) (List.replicate N tick)
      let R := Function.update C (r 12) ((ids.map keep).map bitSymbol)
      S.R (r 0) = (List.range N).flatMap word ++ tail →
      (∀ i < N, (word i).length = W) →
      (∀ i ∈ ([2,3,4,5,6,7,9,10,11,12,13] : List (Fin 15)), S.R (r i) = []) →
      ∃ z n, z.user = u.user ∧ n ≤ (44*LabelMask.records v+13*w+14) + (N*(time (prime^(w-1)) (m*m) 1+5)+4 +
        (8*w+8+22*B + (N*B*(9*L+15)+6+(N*(B*(8*W+11)+6*W+15)+6+N*B*(6*(W+L)+13)+6)))) ∧
        Exec body p (mk u S) n (mk z {S with R := Function.update (Function.update
          (LabelDirectorySetup.prepared R r L) (r 0) tail) (r 14) (ids.flatMap
          (LabelDirectory.entry (fun k => word (k/B)) m w) ++ S.R (r 14))}) := by
  obtain ⟨p,hp⟩ := realizes (body := body) m hm branch r atom one ha ho rs hk hr
  refine ⟨.seq (LabelSpectators.program m beforeRows rows beforeH atom (r 2) (r 9) (r 3) (r 5)) p,?_⟩
  intro v w D hw positive hv word tail u S hbr hrows hbh atomWidth unit ready N L B W ids keep C R source width fresh
  obtain ⟨u',n,hu,hn,he⟩ := LabelSpectators.runs body m hm beforeRows rows beforeH atom
    (r 2) (r 9) (r 3) (r 5) layout v positive w D hv u S hbr hrows hbh atomWidth (by
      intro k h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> apply fresh <;> simp)
  let M : Stacks T prime := {S with R := C}
  have off (k : Fin T) (h : k ∈ slots rs) : k ≠ r 9 := by
    rintro rfl
    exact hr.notMem (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have bank : LabelTraversal.ready (prime^(w-1)) M.R rs := by
    intro pair mem
    have left := off pair.1 (List.mem_flatMap.mpr ⟨pair,mem,by simp⟩)
    have right := off pair.2 (List.mem_flatMap.mpr ⟨pair,mem,by simp⟩)
    simpa [M,C,left,right] using ready pair mem
  obtain ⟨z,t,hz,ht,run⟩ := hp v w D hw hv word tail u' M (by simpa [M,C,ha] using atomWidth)
    (by simpa [M,C,ho] using unit) bank (by simp [M,C,N]) (by simpa [M,C] using source)
    (by simpa [M,C,W] using width) (by
      intro i hi
      have ne : i ≠ 9 := by rintro rfl; simp at hi
      simp only [M,C,Function.update_of_ne (r.injective.ne ne)]
      apply fresh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨z,n+t,hz.trans hu,Nat.add_le_add hn (by simpa [M,C,W] using ht),?_⟩
  simpa [M,C,R] using Exec.seq he run

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryClasses
