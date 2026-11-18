module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryJoin

/-! Expand a parent prefix over its consecutive child label records. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryInherit
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open Host Node LabelCycle IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Consume one parent prefix and append a reversed copy for each child to the accumulator. -/
def parent (r : Fin 8 ↪ Fin T) : Pr P T Q A U :=
  .seq (transfer (r 1) (r 0) (r 2) (r 3))
    (.seq (repeatBlock (r 4) (r 5) (bcopy (r 2) (r 7) (r 3) (r 6))) (uclear (r 2)))

theorem parent_exec (r : Fin 8 ↪ Fin T) (word tail : List (Fin (A+4)))
    (u : HS T Q A U) (S : Stacks T A) (hw : (S.R (r 1)).length = word.length)
    (hs : S.R (r 0) = word ++ tail) (hf : ∀ i ∈ ([2,3,5,6] : List (Fin 8)), S.R (r i) = []) :
    let B := (S.R (r 4)).length
    ∃ v n, v.user = u.user ∧ n ≤ B*(6*word.length+11)+6*word.length+10 ∧
      Exec body (parent r) (mk u S) n (mk v {S with R := Function.update (Function.update S.R (r 0) tail) (r 7) ((List.replicate B word).flatten.reverse ++ S.R (r 7))}) := by
  intro B
  obtain ⟨v,hu,he⟩ := transfer_exec (body := body) (count := r 1) (src := r 0) (dst := r 2)
    (tmp := r 3) (by simp) u S word tail hs hw (hf 3 (by simp))
  rw [hf 2 (by simp),List.append_nil] at he
  let M : Stacks T A := {S with R := Function.update (Function.update S.R (r 0) tail) (r 2) word.reverse}
  obtain ⟨v',n,hu',hn,he'⟩ := repeat_exec body (count := r 4) (saved := r 5) (out := r 7)
    (by simp) (bcopy (r 2) (r 7) (r 3) (r 6)) word.reverse (6*word.length+6) v M
    (by simp [M,hf 5 (by simp)]) (by
      intro t N same
      have eq (i : Fin 8) (h4 : i ≠ 4) (h5 : i ≠ 5) (h7 : i ≠ 7) :
          N.R (r i) = M.R (r i) := same _ (by simpa) (by simpa) (by simpa)
      obtain ⟨t',ht,run⟩ := bcopy_exec (body := body) (a := r 2) (c := r 7)
        (t₁ := r 3) (t₂ := r 6) (by simp) t N
        (by simp [eq 3 (by decide) (by decide) (by decide),M,hf 3 (by simp)])
        (by simp [eq 6 (by decide) (by decide) (by decide),M,hf 6 (by simp)])
      simp only [eq 2 (by decide) (by decide) (by decide),M,Function.update_self,List.length_reverse] at run
      exact ⟨t',_,ht,le_rfl,run⟩)
  have count : (M.R (r 4)).length = B := by simp [M,B]
  rw [count] at he'
  let N : Stacks T A := {M with R := Function.update M.R (r 7) ((List.replicate B word.reverse).flatten ++ M.R (r 7))}
  obtain ⟨v'',hu'',he''⟩ := uclear_exec (body := body) (r 2) v' N
  have len : (N.R (r 2)).length = word.length := by simp [N,M]
  have copies : (List.replicate B word).flatten.reverse = (List.replicate B word.reverse).flatten := by
    simp [List.reverse_flatten]
  refine ⟨v'',_,hu''.trans (hu'.trans hu),?_,(Exec.seq he (Exec.seq he' he'')).cast rfl ?_⟩
  · simp [M] at hn
    rw [len]; dsimp [B]; nlinarith
  · apply congrArg (mk v'')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h : k = r 2
    · subst k; simp [hf 2 (by simp)]
    by_cases h7 : k = r 7
    · subst k; simp [N,M,copies]
    simp [M,N,h,h7]

/-- In physical order each consecutive block of child labels inherits one parent word. -/
theorem child_order (word : ℕ → List α) (parents B : ℕ) :
    (List.range (parents*B)).flatMap (fun j => word (j/B)) =
      (List.range parents).flatMap (fun i => (List.replicate B (word i)).flatten) := by
  induction parents with
  | zero => simp
  | succ p ih =>
    rw [Nat.succ_mul,List.range_add,List.flatMap_append,ih,List.range_succ,List.flatMap_append]
    simp only [List.flatMap_singleton,List.flatMap_map]
    congr 1
    rw [List.flatMap_def,← List.length_range (n := B),← List.map_const']
    apply congrArg List.flatten
    simp only [List.length_range]
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    simp [Nat.mul_comm p B,Nat.mul_add_div (show 0 < B by omega),
      Nat.div_eq_of_lt hj']

/-- Iterate through the parent directory, consuming one count symbol per parent. -/
theorem expand_exec (r : Fin 8 ↪ Fin T) (count saved : Fin T) (hne : count ≠ saved)
    (hc : ∀ i, r i ≠ count) (ht : ∀ i, r i ≠ saved) (word : ℕ → List (Fin (A+4)))
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A) :
    let N := (S.R count).length
    let B := (S.R (r 4)).length
    let W := (S.R (r 1)).length
    S.R (r 0) = (List.range N).flatMap word ++ tail →
    (∀ i < N, (word i).length = W) → (∀ i ∈ ([2,3,5,6] : List (Fin 8)), S.R (r i) = []) →
    ∃ u F n, u.user = v.user ∧ n ≤ N*(B*(6*W+11)+6*W+13)+2 ∧
      Exec body (eachSym count saved (parent r)) (mk v S) n (mk u {S with R := F}) ∧
      F count = [] ∧ F saved = (S.R count).reverse ++ S.R saved ∧
      ∀ k, k ≠ count → k ≠ saved → F k = Function.update (Function.update S.R (r 0) tail)
        (r 7) (((List.range (N*B)).flatMap (fun j => word (j/B))).reverse ++ S.R (r 7)) k := by
  intro N B W hs hw hf
  let ids := List.range N
  let block i := (List.replicate B (word i)).flatten
  let R j := Function.update (Function.update S.R (r 0) ((ids.drop j).flatMap word ++ tail))
    (r 7) (((ids.take j).flatMap block).reverse ++ S.R (r 7))
  have spec : SymSpec body (parent r) count saved (S.R count) R (B*(6*W+11)+6*W+10) := by
    intro j hj u M _ hM
    have slot (i : Fin 8) := hM (r i) (hc i) (ht i)
    have idx : j < ids.length := by simpa [ids,N] using hj
    have drop : ids.drop j = j :: ids.drop (j+1) := by
      rw [List.drop_eq_getElem_cons idx]; simp [ids]
    have take : ids.take (j+1) = ids.take j ++ [j] := by
      simpa only [ids,List.getElem_range] using List.take_succ_eq_append_getElem idx
    obtain ⟨u',n,hu,hn,he⟩ := parent_exec (body := body) r (word j)
      ((ids.drop (j+1)).flatMap word ++ tail) u M (by simp [slot,R,hw j hj,W])
      (by simp [slot,R,drop,List.append_assoc]) (by
        intro i hi
        have h0 : i ≠ 0 := by rintro rfl; simp at hi
        have h7 : i ≠ 7 := by rintro rfl; simp at hi
        simpa [slot,R,h0,h7] using hf i hi)
    have cnt : (M.R (r 4)).length = B := by simp [slot,R,B]
    refine ⟨u',_,n,hu,by simpa [cnt,hw j hj] using hn,he,by simp [(hc _).symm],
      by simp [(ht _).symm],?_⟩
    intro k hkc hkt
    by_cases h7 : k = r 7
    · subst k; simp [R,take,block,slot,B,List.append_assoc]
    by_cases h0 : k = r 0
    · subst k; simp [R]
    simpa [R,h0,h7] using hM k hkc hkt
  obtain ⟨u,F,n,hu,hn,he,hc',ht',hF⟩ := eachSym_exec body hne v S spec (by
    intro k _ _
    by_cases h : k = r 0
    · subst k; simpa [R,ids] using hs
    by_cases h7 : k = r 7
    · subst k; simp [R]
    simp [R,h,h7])
  refine ⟨u,F,n,hu,hn,he,hc',ht',?_⟩
  intro k hkc hkt
  have drop : ids.drop N = [] := List.drop_eq_nil_of_le (by simp [ids])
  have take : ids.take N = ids := List.take_of_length_le (by simp [ids])
  simpa only [R,← show N = (S.R count).length from rfl,drop,take,List.flatMap_nil,List.nil_append,
    child_order,ids,block] using hF k hkc hkt

/-- Replace parent prefixes in place by their child copies and restore the count tape. -/
def expand (r : Fin 8 ↪ Fin T) (count saved : Fin T) : Pr P T Q A U :=
  .seq (eachSym count saved (parent r)) (.seq (moveR saved count id) (moveR (r 7) (r 0) id))

theorem expand_in_place (r : Fin 8 ↪ Fin T) (count saved : Fin T) (hne : count ≠ saved)
    (hc : ∀ i, r i ≠ count) (ht : ∀ i, r i ≠ saved) (word : ℕ → List (Fin (A+4)))
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A) :
    let N := (S.R count).length
    let B := (S.R (r 4)).length
    let W := (S.R (r 1)).length
    let copies := (List.range (N*B)).flatMap fun j => word (j/B)
    S.R (r 0) = (List.range N).flatMap word ++ tail →
    (∀ i < N, (word i).length = W) → (∀ i ∈ ([2,3,5,6,7] : List (Fin 8)), S.R (r i) = []) →
    S.R saved = [] →
    ∃ u n, u.user = v.user ∧ n ≤ N*(B*(8*W+11)+6*W+15)+6 ∧
      Exec body (expand r count saved) (mk v S) n
        (mk u {S with R := Function.update S.R (r 0) (copies ++ tail)}) := by
  intro N B W copies hs hw hf hsave
  obtain ⟨u,F,n,hu,hn,he,hc',ht',hF⟩ := expand_exec (body := body) r count saved hne hc ht word tail v S
    hs hw (fun i hi => hf i (List.mem_append_left [7] hi))
  rw [hsave,List.append_nil] at ht'
  let M : Stacks T A := {S with R := F}
  let H : Stacks T A := {M with R := movedR F saved count id (F saved)}
  obtain ⟨u',hu',he'⟩ := moveR_exec body saved count hne.symm id u M
  obtain ⟨u'',hu'',he''⟩ := moveR_exec body (r 7) (r 0) (by simp) id u' H
  have orig (i : Fin 8) := hF (r i) (hc i) (ht i)
  have acc : H.R (r 7) = copies.reverse := by simp [H,movedR,hc,ht,orig 7,hf 7 (by simp),copies,N,B]
  have src : H.R (r 0) = tail := by simp [H,movedR,hc,ht,orig 0]
  have len : copies.length = N*B*W := by
    unfold copies
    rw [List.flatMap_def,List.length_flatten,List.map_map]
    have eq : (List.range (N*B)).map (List.length ∘ fun j => word (j/B)) =
        (List.range (N*B)).map (fun _ => W) := by
      apply List.map_congr_left
      intro j hj
      have lt := List.mem_range.mp hj
      have pos : 0 < B := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at lt
      exact hw _ ((Nat.div_lt_iff_lt_mul pos).mpr lt)
    simp [eq]
  refine ⟨u'',_,hu''.trans (hu'.trans hu),?_,(Exec.seq he (Exec.seq he' he'')).cast rfl ?_⟩
  · simp only [M,ht',List.length_reverse,acc,len]
    change n ≤ N*(B*(6*W+11)+6*W+13)+2 at hn
    change n+(2*N+2+(2*(N*B*W)+2)) ≤ _
    nlinarith
  · apply congrArg (mk u'')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h0 : k = r 0
    · subst k; simp [movedR,acc,src]
    by_cases h7 : k = r 7
    · subst k; simp [movedR,hf 7 (by simp)]
    by_cases hcount : k = count
    · subst k; simp [movedR,H,h0,h7,ht',hc']
    by_cases hsaved : k = saved
    · subst k; simp [movedR,H,h0,h7,hcount,hsave]
    simp [movedR,H,h0,h7,hcount,hsaved,hF k hcount hsaved]

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

open IntegerMultBounds.Networks.Shared50ModularControl (prime_prime)

/-- Expand the parent stream in place, then consume it alongside the current label stream. -/
theorem directory_exec {body : P → Pr P T Q prime U} (r j : Fin 8 ↪ Fin T)
    (src : r 0 = j 0) (width : r 1 = j 2) (count saved out : Fin T) (hne : count ≠ saved)
    (hc : ∀ i, r i ≠ count) (ht : ∀ i, r i ≠ saved) (apart : ∀ i, out ≠ j i)
    (m w : ℕ) (word : ℕ → List (Fin (prime+4))) (a b : List (Fin (prime+4)))
    (v : HS T Q prime U) (S : Stacks T prime) :
    let N := (S.R count).length
    let B := (prime^w)^(m*m)
    let W := (S.R (r 1)).length
    let L := w*(m*m)
    (S.R (r 4)).length = B → (S.R (j 6)).length = N*B →
    S.R (r 0) = (List.range N).flatMap word ++ a → (∀ i < N, (word i).length = W) →
    S.R (j 1) = LabelDirectoryLoop.words prime_prime.two_le
      (RadixCounterData.zeros prime_prime.two_le L) (N*B) ++ b →
    (S.R (j 3)).length = L → (∀ i ∈ ([2,3,5,6,7] : List (Fin 8)), S.R (r i) = []) →
    S.R saved = [] → (∀ i ∈ ([4,5,7] : List (Fin 8)), S.R (j i) = []) →
    ∃ u n, u.user = v.user ∧ n ≤ N*(B*(8*W+11)+6*W+15)+6 + N*B*(6*(W+L)+13)+6 ∧
      Exec body (.seq (expand r count saved) (LabelDirectoryJoin.program j out)) (mk v S) n
        (mk u {S with R := Function.update (Function.update (Function.update S.R (j 0) a) (j 1) b) out ((List.range (N*B)).flatMap (LabelDirectory.entry (fun k => word (k/B)) m w) ++ S.R out)}) := by
  intro N B W L hB hN hs hw hl hL hf hsave hj
  obtain ⟨u,n,hu,hn,he⟩ := expand_in_place (body := body) r count saved hne hc ht word a v S hs hw hf hsave
  rw [hB] at hn he
  rw [src] at he
  let copies := (List.range (N*B)).flatMap fun k => word (k/B)
  let M : Stacks T prime := {S with R := Function.update S.R (j 0) (copies ++ a)}
  have children : (M.R (j 6)).length = N*B := by simpa [M] using hN
  have W' : (M.R (j 2)).length = W := by simp [M,W,width]
  obtain ⟨u',t,hu',hcost,run⟩ := LabelDirectoryJoin.directory_exec (body := body)
    j out apart m w (fun k => word (k/B)) u M a b (by simp [M,copies,hN])
    (by simpa [M,hN,L] using hl) (by
      intro k hk
      rw [children] at hk
      rw [W']
      exact hw _ ((Nat.div_lt_iff_lt_mul (pow_pos (pow_pos prime_prime.pos w) (m*m))).mpr hk))
    (by simpa [M] using hL) (by
      intro i hi
      have ne : i ≠ 0 := by rintro rfl; simp at hi
      simpa [M,ne] using hj i hi)
  rw [children,W'] at hcost
  refine ⟨u',n+t,hu'.trans hu,by dsimp [W,L,N] at *; omega,?_⟩
  simpa only [children,M,Function.update_idem,Function.update_of_ne (apart 0)] using Exec.seq he run

/-- The ancestor source consumed by the directory join, grouped by parent. -/
theorem join_source (m w parents : ℕ) (word : ℕ → List (Fin (prime+4))) :
    let B := (prime^w)^(m*m)
    (List.range (parents*B)).flatMap (fun j => word (j/B)) =
      (List.range parents).flatMap (fun i => (List.replicate B (word i)).flatten) :=
  child_order word parents _

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryInherit
