module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryCaller
public import IntegerMultBounds.MathlibTM2.Host.CountSelectors

/-! Route child payloads and their prefix directory by a single residue traversal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelChildStreams
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Host Node LabelTraversal RecursiveInterchangeLayout
variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q prime U}

/-- Retain both child record counts for the two subsequent calls. -/
def counts (r : Fin 21 ↪ Fin T) : Pr P T Q prime U :=
  .seq (countSelectors (r 12) (r 2) (r 3) symBit)
    (countSelectors (r 12) (r 2) (r 5) (fun x => !(symBit x)))

private theorem counts_exec (r : Fin 21 ↪ Fin T) (ids : List ℕ) (keep : ℕ → Bool)
    (u : HS T Q prime U) (S : Stacks T prime) (mask : S.R (r 12) = (ids.map keep).map bitSymbol)
    (fresh : ∀ i ∈ ([2,3,5] : List (Fin 21)), S.R (r i) = []) :
    ∃ z n, z.user = u.user ∧ n ≤ 14*ids.length+8 ∧
      Exec body (counts r) (mk u S) n (mk z {S with R := Function.update (Function.update S.R
        (r 3) (List.replicate (ids.filter keep).length tick)) (r 5) (List.replicate (ids.filter (fun k => !(keep k))).length tick)}) := by
  obtain ⟨u',n,hu,hn,he⟩ := countSelectors_exec (body := body) (src := r 12)
    (saved := r 2) (dst := r 3) (by simp) symBit u S (fresh 2 (by decide))
  simp [mask,List.filter_map,Function.comp_def,fresh 3 (by decide)] at he hn
  let M : Stacks T prime := {S with R := Function.update S.R (r 3) (List.replicate (ids.filter keep).length tick)}
  obtain ⟨z,t,hz,ht,run⟩ := countSelectors_exec (body := body) (src := r 12)
    (saved := r 2) (dst := r 5) (by simp) (fun x => !(symBit x)) u' M (by simp [M,fresh 2 (by decide)])
  simp [M,mask,List.filter_map,Function.comp_def,fresh 5 (by decide)] at run ht
  exact ⟨z,n+t,hz.trans hu,by omega,Exec.seq he run⟩

theorem realizes (m : ℕ) (hm : 0 < m) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool)
    (r : Fin 21 ↪ Fin T) (rs : List (Pair T)) (hk : rs.length = m*m)
    (streams : Fin 3 ↪ Fin T) (outside : ∀ i k, streams i ≠ r k)
    (free : ∀ i, streams i ∉ slots rs)
    (hd : (slots rs).Nodup) (apart : ∀ i, r i ∉ slots rs) :
    ∃ p : Pr P T Q prime U, ∀ (v : Descriptor) (w D : ℕ), 0 < w → v.Positive →
      v.beforeH = D*prime^(m*(w*m)) → ∀ (word : ℕ → List (Fin (prime+4)))
      (tail rest : List (Fin (prime+4))) (data : ℕ → List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime),
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
      (∀ i ∈ ([2,3,4,5,6,7,9,10,11,12,13,20] : List (Fin 21)), S.R (r i) = []) →
      S.R (streams 0) = ids.flatMap data ++ rest → (S.R (streams 1)).length = V →
      (∀ i ∈ ids, (data i).length = V) →
      ∃ z F n, z.user = u.user ∧
        F.R (r 7) = good.flatMap entry ++ bad.flatMap entry ++ S.R (r 7) ∧
        F.R (streams 2) = good.flatMap data ++ bad.flatMap data ++ S.R (streams 2) ∧
        F.R (streams 0) = S.R (streams 0) ∧ F.R (r 12) = (ids.map keep).map bitSymbol ∧
        F.R (r 3) = List.replicate good.length tick ∧ F.R (r 5) = List.replicate bad.length tick ∧
        F.R (streams 1) = S.R (streams 1) ∧ (∀ i ∈ ([2,6,13] : List (Fin 21)), F.R (r i) = []) ∧
        F.R (r 8) = S.R (r 8) ∧
        n ≤ (26*H+6 + ((44*LabelMask.records v+13*w+14) +
          (N*(time H (m*m) 1+5)+4 + (8*w+8+22*B + (N*B*(9*L+15)+6+
          (N*(B*(8*W+11)+6*W+15)+6+N*B*(6*(W+L)+13)+6)))))) +
          (4*L+4+2*(ids.length*(16*(W+L)+10)+16)) + 2*(ids.length*(16*V+10)+16) + (14*ids.length+8) ∧
        Exec body p (mk u S) n (mk z F) := by
  obtain ⟨p,hp⟩ := LabelDirectoryCaller.realizes (body := body) m hm branch r rs hk hd apart
  refine ⟨.seq (.seq p (LabelSplit.program (streams 0) (r 12) (streams 1) (r 2) (r 3) (r 5) (r 6) (streams 2))) (counts r),?_⟩
  intro v w D hw positive hv word tail rest data u S hbr hrows hbh atomWidth unit empty N L B W ids keep good bad entry V H source width fresh stock vol sizes
  obtain ⟨u',n,hu,hn,he⟩ := hp v w D hw positive hv word tail u S hbr hrows hbh atomWidth unit empty source width fresh
  let bank := LabelCountBank.fill (rs.map Prod.fst) H (Function.update S.R (r 20) (List.replicate H tick))
  let masks := Function.update (Function.update bank (r 9) (List.replicate N tick)) (r 12) ((ids.map keep).map bitSymbol)
  let R := LabelDirectorySetup.prepared masks ((Fin.castLEEmb (by decide : 15 ≤ 21)).trans r) L
  let Dreg := Function.update (Function.update R (r 0) tail) (r 14) (ids.flatMap entry ++ S.R (r 14))
  let M : Stacks T prime := {S with R := Function.update (Function.update Dreg (r 1)
    (List.replicate L tick ++ S.R (r 1))) (r 7) (good.flatMap entry ++ bad.flatMap entry ++ S.R (r 7))}
  have off (k : Fin T) (h : k ∉ slots rs) : k ∉ rs.map Prod.fst := by
    intro mem
    obtain ⟨pair,hp,eq⟩ := List.mem_map.mp mem
    exact h (eq ▸ List.mem_flatMap.mpr ⟨pair,hp,by simp⟩)
  have same (i : Fin 3) : M.R (streams i) = S.R (streams i) := by
    simp [M,Dreg,R,LabelDirectorySetup.prepared,masks,bank,LabelCountBank.fill,outside,off _ (free i)]
  have mask : M.R (r 12) = (ids.map keep).map bitSymbol := by
    simp [M,Dreg,R,LabelDirectorySetup.prepared,masks]
  have scratch (i : Fin 21) (hi : i ∈ ([2,3,5,6] : List (Fin 21))) : M.R (r i) = [] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [M,Dreg,R,LabelDirectorySetup.prepared,masks,bank,LabelCountBank.fill,off _ (apart _),fresh]
  obtain ⟨z,t,hz,ht,run⟩ := LabelSplit.split_exec (body := body) (src := streams 0) (mask := r 12)
    (width := streams 1) (symbols := r 2) (ts := r 3) (tm := r 5) (acc := r 6) (out := streams 2)
    (by simp [outside,fun i k => (outside i k).symm]) ids keep data V sizes u' M rest
    ((same 0).trans stock) mask (by rwa [same]) (by
      intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> apply scratch <;> decide)
  let J : Stacks T prime := {M with R := Function.update M.R (streams 2) (good.flatMap data ++ bad.flatMap data ++ M.R (streams 2))}
  have kept : J.R (r 12) = (ids.map keep).map bitSymbol := by simp [J,(outside 2 12).symm,mask]
  obtain ⟨z',c,hz',hc,countRun⟩ := counts_exec (body := body) r ids keep z J kept (by
    intro i hi
    simp only [J,Function.update_of_ne (outside 2 i).symm]
    apply scratch
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide)
  refine ⟨z',_,n+t+c,hz'.trans (hz.trans hu),?_,?_,?_,?_,?_,?_,?_,?_,?_,Nat.add_le_add (Nat.add_le_add hn ht) hc,
    Exec.seq (Exec.seq he run) countRun⟩
  · simp [J,M,(outside 2 7).symm]
  · simp [J,outside,same]
  · simp [J,outside,same]
  · simp [kept]
  · simp [good]
  · simp [bad]
  · simp [J,outside,same]
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp [J,M,Dreg,R,LabelDirectorySetup.prepared,masks,bank,LabelCountBank.fill,
        (outside _ _).symm,off _ (apart _),fresh]

  · simp [J,M,Dreg,R,LabelDirectorySetup.prepared,masks,bank,LabelCountBank.fill,
      (outside 2 8).symm,off _ (apart _)]

end
end IntegerMultBounds.MathlibTM2.Cover.LabelChildStreams
