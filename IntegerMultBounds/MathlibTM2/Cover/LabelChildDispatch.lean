module

public import IntegerMultBounds.MathlibTM2.Cover.LabelChildCalls

/-! Split, call both child procedures and merge their results on one shared host layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelChildDispatch
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Host Node LabelTraversal RecursiveInterchangeLayout
variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q prime U}

def streams : Fin 3 ↪ Fin 24 := ⟨![21,22,23],by decide⟩
def calls : Fin 12 ↪ Fin 24 := ⟨![4,10,22,12,2,6,13,8,7,23,3,5],by decide⟩

theorem realizes (m : ℕ) (hm : 0 < m) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool)
    (r : Fin 24 ↪ Fin T) (rs : List (Pair T)) (hk : rs.length = m*m)
    (hd : (slots rs).Nodup) (apart : ∀ i, r i ∉ slots rs) (g b : P) :
    ∃ p : Pr P T Q prime U, ∀ (v : Descriptor) (w D : ℕ), 0 < w → v.Positive →
      v.beforeH = D*prime^(m*(w*m)) → ∀ (word : ℕ → List (Fin (prime+4)))
      (tail rest : List (Fin (prime+4))) (data outG outB : ℕ → List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime),
      (S.R (r 17)).length = v.beforeRows → (S.R (r 18)).length = v.rows →
      (S.R (r 19)).length = v.beforeH → S.R (r 15) = List.replicate w tick → (S.R (r 16)).length = 1 → (∀ k ∈ slots rs, S.R k = []) →
      let N := v.beforeRows*v.rows*D
      let L := w*(m*m)
      let B := prime^L
      let W := (S.R (r 1)).length
      let ids := List.range (N*B)
      let keep := fun k => branch (LabelStock.residue m w 1 k)
      let good := ids.filter keep
      let bad := ids.filter (fun k => !(keep k))
      let entry := LabelDirectory.entry (fun k => word (k/B)) m w
      let V := LabelTransport.payload v
      let H := prime^(w-1)
      S.R (r 0) = (List.range N).flatMap word ++ tail → (∀ i < N, (word i).length = W) →
      (∀ i ∈ ([2,3,4,5,6,7,9,10,11,12,13,20] : List (Fin 24)), S.R (r i) = []) →
      S.R (r 21) = ids.flatMap data ++ rest → (S.R (r 22)).length = V →
      (∀ i ∈ ids, (data i).length = V) →
      ∀ cg cb, LabelChildCalls.Child body g (r 7) (r 23) (r 3) (r 4) good entry data outG cg (r 1) (W+L) →
      LabelChildCalls.Child body b (r 7) (r 23) (r 5) (r 10) bad entry data outB cb (r 1) (W+L) →
      (∀ j ∈ good, (outG j).length = V) → (∀ j ∈ bad, (outB j).length = V) →
      let result := ids.flatMap fun j => if keep j then outG j else outB j
      ∃ z F n, z.user = u.user ∧ F.R (r 21) = S.R (r 21) ∧ F.R (r 8) = result ++ S.R (r 8) ∧
        n ≤ ((26*H+6 + ((44*LabelMask.records v+13*w+14) +
          (N*(time H (m*m) 1+5)+4 + (8*w+8+22*B + (N*B*(9*L+15)+6+
          (N*(B*(8*W+11)+6*W+15)+6+N*B*(6*(W+L)+13)+6)))))) +
          (4*L+4+2*(ids.length*(16*(W+L)+10)+16)) + 2*(ids.length*(16*V+10)+16) + (14*ids.length+8)) + (cg+cb+ids.length*(6*V+10)+10) ∧ Exec body p (mk u S) n (mk z F) := by
  let dir := (Fin.castLEEmb (by decide : 21 ≤ 24)).trans r
  let dataSlots := streams.trans r
  have outside (i : Fin 3) (k : Fin 21) : dataSlots i ≠ dir k :=
    r.injective.ne (by revert i k; decide)
  obtain ⟨p,hp⟩ := LabelChildStreams.realizes (body := body) m hm branch dir rs hk dataSlots
    outside (fun i => apart _) hd (fun i => apart _)
  refine ⟨.seq p (LabelChildCalls.program (calls.trans r) g b),?_⟩
  intro v w D hw positive hv word tail rest data outG outB u S hbr hrows hbh atomWidth unit empty N L B W ids keep good bad entry V H source width fresh stock vol sizes cg cb runG runB sizeG sizeB result
  obtain ⟨u',M,n,hu,hdir,hdata,hsrc,hmask,hg,hb,hwidth,hscratch,hout,hentryWidth,hn,he⟩ :=
    hp v w D hw positive hv word tail rest data u S hbr hrows hbh atomWidth unit empty source width
      (by intro i hi; apply fresh; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      stock vol sizes
  obtain ⟨z,t,hz,ht,run⟩ := LabelChildCalls.calls_exec (body := body) (calls.trans r) (r 1) (fun i => r.injective.ne (by revert i; decide)) (W+L) g b ids keep entry data outG outB V cg cb sizeG sizeB u' M
    (S.R (r 7)) (S.R (r 23)) runG runB (by change (M.R (dir 1)).length = _; rw [hentryWidth,List.length_append,List.length_replicate]; exact Nat.add_comm ..) hdir hdata (by change (M.R (dir 3)).length = _; rw [hg,List.length_replicate])
    (by change (M.R (dir 5)).length = _; rw [hb,List.length_replicate]) hmask (hwidth ▸ vol) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact hscratch 2 (by decide)
      · exact hscratch 6 (by decide)
      · exact hscratch 13 (by decide))
  refine ⟨z,_,n+t,hz.trans hu,?_,?_,Nat.add_le_add hn ht,Exec.seq he run⟩
  · simpa [calls,dataSlots,streams] using hsrc
  · simpa [calls,result,dir] using congrArg (result ++ ·) hout

end
end IntegerMultBounds.MathlibTM2.Cover.LabelChildDispatch
