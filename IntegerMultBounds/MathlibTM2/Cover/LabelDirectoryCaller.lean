module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryClasses
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Cover.LabelCountBank

/-! Construct the directory from unary caller dimensions and empty selector counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryCaller
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open Host Node LabelTraversal RecursiveInterchangeLayout
variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q prime U}

private theorem build (m : ℕ) (hm : 0 < m) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool)
    (r : Fin 21 ↪ Fin T) (rs : List (Pair T)) (hk : rs.length = m*m)
    (hd : (slots rs).Nodup) (apart : ∀ i, r i ∉ slots rs) :
    ∃ p : Pr P T Q prime U, ∀ (v : Descriptor) (w D : ℕ), 0 < w → v.Positive →
      v.beforeH = D*prime^(m*(w*m)) → ∀ (word : ℕ → List (Fin (prime+4)))
      (tail : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime),
      (S.R (r 17)).length = v.beforeRows → (S.R (r 18)).length = v.rows →
      (S.R (r 19)).length = v.beforeH → S.R (r 15) = List.replicate w tick → (S.R (r 16)).length = 1 → (∀ k ∈ slots rs, S.R k = []) →
      let N := v.beforeRows*v.rows*D
      let L := w*(m*m)
      let B := prime^L
      let W := (S.R (r 1)).length
      let ids := List.range (N*B)
      let keep := fun k => branch (LabelStock.residue m w 1 k)
      let H := prime^(w-1)
      let F := LabelCountBank.fill (rs.map Prod.fst) H (Function.update S.R (r 20) (List.replicate H tick))
      let C := Function.update F (r 9) (List.replicate N tick)
      let R := Function.update C (r 12) ((ids.map keep).map bitSymbol)
      S.R (r 0) = (List.range N).flatMap word ++ tail →
      (∀ i < N, (word i).length = W) →
      (∀ i ∈ ([2,3,4,5,6,7,9,10,11,12,13,20] : List (Fin 21)), S.R (r i) = []) →
      ∃ z n, z.user = u.user ∧ n ≤ 26*H+6 + ((44*LabelMask.records v+13*w+14) + (N*(time (prime^(w-1)) (m*m) 1+5)+4 +
        (8*w+8+22*B + (N*B*(9*L+15)+6+(N*(B*(8*W+11)+6*W+15)+6+N*B*(6*(W+L)+13)+6))))) ∧
        Exec body p (mk u S) n (mk z {S with R := Function.update (Function.update
          (LabelDirectorySetup.prepared R ((Fin.castLEEmb (by decide : 15 ≤ 21)).trans r) L) (r 0) tail) (r 14) (ids.flatMap
          (LabelDirectory.entry (fun k => word (k/B)) m w) ++ S.R (r 14))}) := by
  let dir := (Fin.castLEEmb (by decide : 15 ≤ 21)).trans r
  have port (i : Fin 15) : dir i = r (Fin.castLE (by decide) i) := rfl
  have hr : (r 9 :: r 13 :: (slots rs ++ [r 12])).Nodup := by
    simp [List.nodup_append,hd,apart]
    exact fun k h e => apart 12 (e ▸ h)
  obtain ⟨p,hp⟩ := LabelDirectoryClasses.from_dimensions (body := body) m hm branch dir
    (r 15) (r 16) (fun i => r.injective.ne (by revert i; decide))
    (fun i => r.injective.ne (by revert i; decide))
    (r 17) (r 18) (r 19) (by simp [port]) rs hk hr
  refine ⟨.seq (.seq (LabelCounts.highCount (r 16) (r 15) (r 20) (r 2) (r 3) (r 5))
    (scanR (r 20) (r 2) (LabelCountBank.pushAll (rs.map Prod.fst)))) p,?_⟩
  intro v w D hw positive hv word tail u S hbr hrows hbh atomWidth unit empty N L B W ids keep H F C R source width fresh
  obtain ⟨ready,u',n,hu,hn,he⟩ := LabelCountBank.prepare_exec body rs (r 16) (r 15)
    (r 20) (r 2) (r 3) (r 5) (by simp) (by simp [hd,apart]) u S w hw atomWidth unit (by
      intro k h
      rcases List.mem_append.mp h with h | h
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> apply fresh <;> decide
      · exact empty k h)
  let M : Stacks T prime := {S with R := F}
  have same (i : Fin 21) (hi : i ≠ 20) : M.R (r i) = S.R (r i) := by
    have off : r i ∉ rs.map Prod.fst := by
      rintro h
      obtain ⟨pair,hp,eq⟩ := List.mem_map.mp h
      exact apart i (eq ▸ List.mem_flatMap.mpr ⟨pair,hp,by simp⟩)
    simp [M,F,LabelCountBank.fill,off,hi]
  have small (i : Fin 15) : M.R (dir i) = S.R (dir i) :=
    same _ (by revert i; decide)
  obtain ⟨z,t,hz,ht,run⟩ := hp v w D hw positive hv word tail u' M
    (by rwa [same 17 (by decide)]) (by rwa [same 18 (by decide)]) (by rwa [same 19 (by decide)])
    (by rw [same 15 (by decide),atomWidth,List.length_replicate]) (by rwa [same 16 (by decide)])
    ready (by rw [small]; exact source) (by rw [small]; exact width) (by
      intro i hi
      rw [small]
      apply fresh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [small 1] at ht
  rw [small 14] at run
  exact ⟨z,n+t,hz.trans hu,Nat.add_le_add hn ht,Exec.seq he run⟩

/-- Add the new label width to the inherited width and use it to split complete directory entries. -/
def partition (r : Fin 21 ↪ Fin T) : Pr P T Q prime U :=
  .seq (ucopy (r 11) (r 1) (r 2))
    (LabelSplit.program (r 14) (r 12) (r 1) (r 2) (r 3) (r 5) (r 6) (r 7))

theorem partition_exec (r : Fin 21 ↪ Fin T) (m w : ℕ)
    (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool) (ids : List ℕ)
    (ancestor : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (u : HS T Q prime U) (S : Stacks T prime) :
    let keep := fun j => branch (LabelStock.residue m w 1 j)
    let entry := LabelDirectory.entry ancestor m w
    let W := (S.R (r 1)).length
    let L := w*(m*m)
    let R := Function.update S.R (r 1) (List.replicate L tick ++ S.R (r 1))
    (S.R (r 11)).length = L → (∀ j ∈ ids, (ancestor j).length = W) →
    S.R (r 14) = ids.flatMap entry ++ tail → S.R (r 12) = (ids.map keep).map bitSymbol →
    (∀ i ∈ ([2,3,5,6] : List (Fin 21)), S.R (r i) = []) →
    ∃ z n, z.user = u.user ∧ n ≤ 4*L+4+2*(ids.length*(16*(W+L)+10)+16) ∧
      Exec body (partition r) (mk u S) n (mk z {S with R := Function.update R (r 7) ((ids.filter keep).flatMap entry ++ (ids.filter (fun j => !(keep j))).flatMap entry ++ S.R (r 7))}) := by
  intro keep entry W L R len widths source mask fresh
  obtain ⟨u',hu,he⟩ := ucopy_exec (body := body) (a := r 11) (b := r 1) (t := r 2)
    (by simp) (by simp) (by simp) u S (fresh 2 (by simp))
  rw [len] at he
  let M : Stacks T prime := {S with R := R}
  obtain ⟨z,t,hz,ht,run⟩ := LabelDirectory.split_exec (body := body) (src := r 14)
    (mask := r 12) (width := r 1) (symbols := r 2) (ts := r 3) (tm := r 5) (acc := r 6)
    (out := r 7) (by simp) ids m w W branch ancestor widths u' M tail
    (by simpa [M,R] using source) (by simpa [M,R] using mask)
    (by simp [M,R,W,L,Nat.add_comm]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp [M,R,fresh])
  exact ⟨z,_,hz.trans hu,Nat.add_le_add_left ht _,by simpa only [partition,entry,keep,M,R,Function.update_of_ne (r.injective.ne (by decide : (7 : Fin 21) ≠ 1))] using Exec.seq he run⟩

/-- Initialize, enumerate, and stably partition the recursive directory in one host program. -/
theorem realizes (m : ℕ) (hm : 0 < m) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool)
    (r : Fin 21 ↪ Fin T) (rs : List (Pair T)) (hk : rs.length = m*m)
    (hd : (slots rs).Nodup) (apart : ∀ i, r i ∉ slots rs) :
    ∃ p : Pr P T Q prime U, ∀ (v : Descriptor) (w D : ℕ), 0 < w → v.Positive →
      v.beforeH = D*prime^(m*(w*m)) → ∀ (word : ℕ → List (Fin (prime+4)))
      (tail : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime),
      (S.R (r 17)).length = v.beforeRows → (S.R (r 18)).length = v.rows →
      (S.R (r 19)).length = v.beforeH → S.R (r 15) = List.replicate w tick → (S.R (r 16)).length = 1 → (∀ k ∈ slots rs, S.R k = []) →
      let N := v.beforeRows*v.rows*D
      let L := w*(m*m)
      let B := prime^L
      let W := (S.R (r 1)).length
      let ids := List.range (N*B)
      let keep := fun k => branch (LabelStock.residue m w 1 k)
      let H := prime^(w-1)
      let F := LabelCountBank.fill (rs.map Prod.fst) H (Function.update S.R (r 20) (List.replicate H tick))
      let C := Function.update F (r 9) (List.replicate N tick)
      let R := Function.update C (r 12) ((ids.map keep).map bitSymbol)
      S.R (r 0) = (List.range N).flatMap word ++ tail →
      (∀ i < N, (word i).length = W) →
      (∀ i ∈ ([2,3,4,5,6,7,9,10,11,12,13,20] : List (Fin 21)), S.R (r i) = []) →
      let entry := LabelDirectory.entry (fun k => word (k/B)) m w
      let Dreg := Function.update (Function.update
        (LabelDirectorySetup.prepared R ((Fin.castLEEmb (by decide : 15 ≤ 21)).trans r) L)
        (r 0) tail) (r 14) (ids.flatMap entry ++ S.R (r 14))
      let next := Function.update Dreg (r 1) (List.replicate L tick ++ S.R (r 1))
      ∃ z n, z.user = u.user ∧ n ≤ (26*H+6 + ((44*LabelMask.records v+13*w+14) +
        (N*(time H (m*m) 1+5)+4 + (8*w+8+22*B + (N*B*(9*L+15)+6+
        (N*(B*(8*W+11)+6*W+15)+6+N*B*(6*(W+L)+13)+6)))))) + (4*L+4+2*(ids.length*(16*(W+L)+10)+16)) ∧
        Exec body p (mk u S) n (mk z {S with R := Function.update next (r 7) ((ids.filter keep).flatMap entry ++ (ids.filter (fun k => !(keep k))).flatMap entry ++ S.R (r 7))}) := by
  obtain ⟨p,hp⟩ := build (body := body) m hm branch r rs hk hd apart
  refine ⟨.seq p (partition r),?_⟩
  intro v w D hw positive hv word tail u S hbr hrows hbh atomWidth unit empty N L B W ids keep H F C R source width fresh entry Dreg next
  obtain ⟨u',n,hu,hn,he⟩ := hp v w D hw positive hv word tail u S hbr hrows hbh atomWidth unit empty source width fresh
  let M : Stacks T prime := {S with R := Dreg}
  have off (i : Fin 21) : r i ∉ rs.map Prod.fst := by
    intro h
    obtain ⟨pair,hp,eq⟩ := List.mem_map.mp h
    exact apart i (eq ▸ List.mem_flatMap.mpr ⟨pair,hp,by simp⟩)
  have same (i : Fin 21) (hi : i ∈ ([1,2,3,5,6,7] : List (Fin 21))) : M.R (r i) = S.R (r i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [M,Dreg,LabelDirectorySetup.prepared,R,C,F,LabelCountBank.fill,off]
  have w1 := same 1 (by decide)
  obtain ⟨z,t,hz,ht,run⟩ := partition_exec (body := body) r m w branch ids (fun k => word (k/B))
    (S.R (r 14)) u' M (by simp [M,Dreg,LabelDirectorySetup.prepared,L]) (by
      intro k hk; rw [w1]
      exact width _ ((Nat.div_lt_iff_lt_mul (pow_pos prime_prime.pos L)).mpr
        (List.mem_range.mp hk))) (by simp [M,Dreg,entry])
    (by simp [M,Dreg,LabelDirectorySetup.prepared,R,keep]) (by
      intro i hi
      have mem : i ∈ ([1,2,3,5,6,7] : List (Fin 21)) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> decide
      rw [same i mem]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> apply fresh <;> decide)
  rw [w1] at ht run
  rw [same 7 (by decide)] at run
  exact ⟨z,n+t,hz.trans hu,Nat.add_le_add hn ht,Exec.seq he run⟩

/-- Move the leading child's directory to its scanner queue. The rest of
the partition stays on the source tape for the sibling. -/
theorem takeChild_exec (r : Fin 7 ↪ Fin T) (selected : List ℕ)
    (ancestor : ℕ → List (Fin (prime+4))) (m w a : ℕ)
    (width : ∀ j ∈ selected, (ancestor j).length = a)
    (tail : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime) :
    let word := fun i : ℕ => LabelDirectory.entry ancestor m w (selected[i]?.getD 0)
    let size := selected.length*(a+w*(m*m))
    S.R (r 1) = selected.flatMap (LabelDirectory.entry ancestor m w) ++ tail →
    (S.R (r 5)).length = selected.length → (S.R (r 6)).length = a+w*(m*m) →
    S.R (r 0) = [] → S.R (r 2) = [] → S.R (r 3) = [] → S.R (r 4) = [] →
    ∃ z t, z.user = u.user ∧ t ≤ 10*size+9*selected.length+10 ∧ (∀ i < selected.length, (word i).length = a+w*(m*m)) ∧
      Exec body ((Mult.ShortConv.unaryProduct (r 5) (r 6) (r 0) (r 3) (r 4)).seq
        (Mult.PhaseCellToeplitz.takePrefix (r 0) (r 1) (r 2) (r 3) (r 4)))
        (mk u S) t (mk z {S with R := (Function.update (Function.update
          (Function.update S.R (r 0) (List.replicate size tick)) (r 1) tail)
          (r 2) ((List.range selected.length).flatMap word))}) := by
  intro word size source rows rowWidth count dst buf tmp
  obtain ⟨packed,widths⟩ := LabelDirectory.child_prefixes selected ancestor m w a width
  have volume : (selected.flatMap (LabelDirectory.entry ancestor m w)).length = size := by
    rw [List.flatMap_def,BlockRotationData.uniform_volume (a+w*(m*m)),List.length_map]
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    rw [LabelDirectory.entry_length,width j hj]
  obtain ⟨v,t,user,paid,product⟩ := Mult.ShortConv.unaryProduct_exec (body := body)
    (a := r 5) (b := r 6) (dst := r 0) (t₁ := r 3) (t₂ := r 4) (by simp) u S buf tmp
  rw [rows,rowWidth,count,List.append_nil] at product
  let D : Stacks T prime := {S with R := Function.update S.R (r 0) (List.replicate size tick)}
  obtain ⟨z,same,run⟩ := Mult.PhaseCellToeplitz.takePrefix_exec (body := body)
    (count := r 0) (src := r 1) (dst := r 2) (buf := r 3) (tmp := r 4)
    (by simp) v D _ tail (by simpa [D] using source) (by simp [D,volume])
    (by simpa [D] using buf) (by simpa [D] using tmp)
  refine ⟨z,t+(6*size+6),same.trans user,?_,widths,Exec.seq product ?_⟩
  · rw [rows,rowWidth,Nat.mul_add] at paid
    dsimp only [size]
    rw [← Nat.mul_assoc,Nat.mul_comm selected.length 4,Nat.mul_assoc] at paid
    omega
  · rw [volume] at run
    simpa [D,dst,packed,word] using run

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryCaller
