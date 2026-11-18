module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryLoop
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Join the inherited prefix and current label of each directory record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryJoin
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open Host Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def joinStep (r : Fin 8 ↪ Fin T) : Pr P T Q A U :=
  .seq (transfer (r 2) (r 0) (r 4) (r 5)) (transfer (r 3) (r 1) (r 4) (r 5))

private theorem step_exec (r : Fin 8 ↪ Fin T) (v : HS T Q A U) (S : Stacks T A)
    (x y a b : List (Fin (A+4))) (hx : S.R (r 0) = x++a) (hy : S.R (r 1) = y++b)
    (hw : (S.R (r 2)).length = x.length) (hl : (S.R (r 3)).length = y.length)
    (ht : S.R (r 5) = []) :
    ∃ v', v'.user = v.user ∧ Exec body (joinStep r) (mk v S) (4*(x.length+y.length)+8)
      (mk v' {S with R := Function.update (Function.update (Function.update S.R (r 0) a) (r 1) b) (r 4) ((x++y).reverse ++ S.R (r 4))}) := by
  obtain ⟨u,hu,he⟩ := transfer_exec (body := body) (count := r 2) (src := r 0) (dst := r 4)
    (tmp := r 5) (by simp) v S x a hx hw ht
  let M : Stacks T A := {S with R := Function.update (Function.update S.R (r 0) a) (r 4) (x.reverse ++ S.R (r 4))}
  obtain ⟨u',hu',he'⟩ := transfer_exec (body := body) (count := r 3) (src := r 1) (dst := r 4)
    (tmp := r 5) (by simp) u M y b (by simpa [M] using hy) (by simpa [M] using hl)
    (by simpa [M] using ht)
  refine ⟨u',hu'.trans hu,(Exec.seq he he').cast (by omega) ?_⟩
  apply congrArg (mk u')
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h : k = r 4 <;> simp [M,h,Function.update_apply,List.append_assoc]

def program (r : Fin 8 ↪ Fin T) (out : Fin T) : Pr P T Q A U :=
  .seq (eachSym (r 6) (r 7) (joinStep r)) (.seq (moveR (r 7) (r 6) id) (moveR (r 4) out id))

theorem join_exec (r : Fin 8 ↪ Fin T) (out : Fin T) (apart : ∀ i, out ≠ r i)
    (v : HS T Q A U) (S : Stacks T A) (x y : ℕ → List (Fin (A+4)))
    (a b : List (Fin (A+4))) (hx : S.R (r 0) = (List.range (S.R (r 6)).length).flatMap x ++ a)
    (hy : S.R (r 1) = (List.range (S.R (r 6)).length).flatMap y ++ b)
    (hw : ∀ s < (S.R (r 6)).length, (x s).length = (S.R (r 2)).length)
    (hl : ∀ s < (S.R (r 6)).length, (y s).length = (S.R (r 3)).length)
    (hf : ∀ i ∈ ([4,5,7] : List (Fin 8)), S.R (r i) = []) :
    let c := S.R (r 6)
    let W := (S.R (r 2)).length + (S.R (r 3)).length
    let joined := (List.range c.length).flatMap fun s => x s ++ y s
    ∃ u n, u.user = v.user ∧ n ≤ c.length*(6*W+13)+6 ∧
      Exec body (program r out) (mk v S) n (mk u {S with R := Function.update (Function.update (Function.update S.R (r 0) a) (r 1) b) out (joined ++ S.R out)}) := by
  intro c W joined
  let ids := List.range c.length
  let z (j : ℕ) := x j ++ y j
  let R j := Function.update (Function.update (Function.update S.R (r 0)
    ((ids.drop j).flatMap x ++ a)) (r 1) ((ids.drop j).flatMap y ++ b)) (r 4)
      (((ids.take j).flatMap z).reverse)
  have spec : SymSpec body (joinStep r) (r 6) (r 7) c R (4*W+8) := by
    intro j hj u M _ hM
    have slot (i : Fin 8) (h6 : i ≠ 6) (h7 : i ≠ 7) : M.R (r i) = R j (r i) :=
      hM _ (by simpa) (by simpa)
    have hidx : j < ids.length := by simpa [ids] using hj
    have hd : ids.drop j = j :: ids.drop (j+1) := by
      rw [List.drop_eq_getElem_cons hidx]; simp [ids]
    obtain ⟨u',hu,he⟩ := step_exec (body := body) r u M (x j) (y j)
      ((ids.drop (j+1)).flatMap x ++ a) ((ids.drop (j+1)).flatMap y ++ b)
      (by simp [slot 0 (by decide) (by decide),R,hd,List.append_assoc])
      (by simp [slot 1 (by decide) (by decide),R,hd,List.append_assoc])
      (by simp [slot 2 (by decide) (by decide),R,hw j hj])
      (by simp [slot 3 (by decide) (by decide),R,hl j hj])
      (by simp [slot 5 (by decide) (by decide),R,hf 5 (by simp)])
    refine ⟨u',_,_,hu,by simp [W,hw j hj,hl j hj],he,by simp,by simp,?_⟩
    intro k hk6 hk7
    by_cases h4 : k = r 4
    · subst k
      have take : ids.take (j+1) = ids.take j ++ [j] := by simpa only [ids,List.getElem_range] using List.take_succ_eq_append_getElem hidx
      simp [R,slot 4 (by decide) (by decide),take,z,List.append_assoc]
    by_cases h1 : k = r 1
    · subst k; simp [R]
    by_cases h0 : k = r 0
    · subst k; simp [R]
    simpa [R,h4,h1,h0] using hM k hk6 hk7
  obtain ⟨u,F,n,hu,hn,he,h6,h7,hF⟩ := eachSym_exec (body := body) (by simp) v S spec (by
    intro k _ _
    by_cases h4 : k = r 4
    · subst k; simp [R,hf 4 (by simp)]
    by_cases h1 : k = r 1
    · subst k; simpa [R,ids,c] using hy
    by_cases h0 : k = r 0
    · subst k; simpa [R,ids,c] using hx
    simp [R,h4,h1,h0])
  rw [hf 7 (by simp),List.append_nil] at h7
  let M : Stacks T A := {S with R := F}
  let M' : Stacks T A := {M with R := movedR F (r 7) (r 6) id (F (r 7))}
  obtain ⟨u',hu',he'⟩ := moveR_exec body (r 7) (r 6) (by simp) id u M
  obtain ⟨u'',hu'',he''⟩ := moveR_exec body (r 4) out (apart 4).symm id u' M'
  have acc : M'.R (r 4) = joined.reverse := by
    simp [M',movedR,hF _ (by simp : r 4 ≠ r 6) (by simp : r 4 ≠ r 7),R,ids,c,joined,z]
  have dst : M'.R out = S.R out := by simp [M',movedR,hF out (apart 6) (apart 7),R,apart]
  have len : joined.length = c.length*W := by
    change (ids.flatMap z).length = _
    rw [List.flatMap_def,List.length_flatten,List.map_map]
    have eq : ids.map (List.length ∘ z) = ids.map (fun _ => W) := by
      apply List.map_congr_left
      intro j hj
      have lt := List.mem_range.mp hj
      simp [z,W,hw j lt,hl j lt]
    simp [eq,ids]
  refine ⟨u'',_,hu''.trans (hu'.trans hu),?_,(Exec.seq he (Exec.seq he' he'')).cast rfl ?_⟩
  · simp only [M,h7,List.length_reverse,acc,len]
    change n ≤ c.length*(4*W+8+3)+2 at hn
    dsimp [c] at *
    nlinarith
  · apply congrArg (mk u'')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases ho : k = out
    · subst k; simp [movedR,acc,dst]
    by_cases h4 : k = r 4
    · subst k; simp [movedR,ho,hf 4 (by simp)]
    by_cases hk6 : k = r 6
    · subst k; simp [movedR,M',ho,h7,h6]
    by_cases hk7 : k = r 7
    · subst k; simp [movedR,M',ho,hf 7 (by simp)]
    have drop : ids.drop (S.R (r 6)).length = [] := List.drop_eq_nil_of_le (by simp [ids,c])
    simp [movedR,M',ho,h4,hk6,hk7,hF k hk6 hk7,R,drop]

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)

/-- Join the generated label stream and the inherited directory in physical record order. -/
theorem directory_exec {body : P → Pr P T Q prime U} (r : Fin 8 ↪ Fin T)
    (out : Fin T) (apart : ∀ i, out ≠ r i) (m w : ℕ) (ancestor : ℕ → List (Fin (prime+4)))
    (v : HS T Q prime U) (S : Stacks T prime) (a b : List (Fin (prime+4))) :
    let N := (S.R (r 6)).length
    let L := w*(m*m)
    let W := (S.R (r 2)).length
    S.R (r 0) = (List.range N).flatMap ancestor ++ a →
    S.R (r 1) = LabelDirectoryLoop.words prime_prime.two_le
      (RadixCounterData.zeros prime_prime.two_le L) N ++ b →
    (∀ j < N, (ancestor j).length = W) → (S.R (r 3)).length = L →
    (∀ i ∈ ([4,5,7] : List (Fin 8)), S.R (r i) = []) →
    ∃ u n, u.user = v.user ∧ n ≤ N*(6*(W+L)+13)+6 ∧
      Exec body (program r out) (mk v S) n
        (mk u {S with R := Function.update (Function.update (Function.update S.R (r 0) a) (r 1) b) out ((List.range N).flatMap (LabelDirectory.entry ancestor m w) ++ S.R out)}) := by
  intro N L W hx hy hw hl hf
  unfold LabelDirectory.entry
  dsimp only [N,W]
  simpa only [hl] using join_exec (body := body) r out apart v S ancestor
    (fun j => (LabelDirectory.digits m w j).map RadixDigits.digitSymbol) a b hx hy hw
    (fun j _ => by simp [LabelDirectory.digits,hl,L]) hf

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryJoin
