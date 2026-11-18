module

public import IntegerMultBounds.MathlibTM2.Cover.LabelCounts

/-! Fill all atom counters in one pass over the high-part count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelCountBank
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Host Node LabelTraversal
variable {T Q A : ℕ} {P U : Type}

def fill (ks : List (Fin T)) (n : ℕ) (R : Regs T A) : Regs T A :=
  fun k => if k ∈ ks then List.replicate n tick ++ R k else R k

def pushAll : List (Fin T) → Act T Q A U → Act T Q A U
  | [], p => p
  | k :: ks, p => .push (.rt k) (fun _ => tick) (pushAll ks p)

private theorem push_run (ks : List (Fin T)) (hd : ks.Nodup) (p : Act T Q A U)
    (v : HS T Q A U) (S : Stacks T A) :
    (pushAll ks p).run (mk v S) = p.run (mk v {S with R := fill ks 1 S.R}) := by
  induction ks generalizing S with
  | nil =>
    have h : fill [] 1 S.R = S.R := by funext j; simp [fill]
    simp [pushAll,h]
  | cons k ks ih =>
    simp only [pushAll,Action.run,mk_var,mk_stk,update_rt,store_mk]
    rw [ih hd.tail]
    congr 2
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j = k
    · subst j; simp [fill,hd.notMem]
    · simp [fill,hj]

theorem copy_exec (body : P → Pr P T Q A U) (src tmp : Fin T) (ks : List (Fin T))
    (hr : (src :: tmp :: ks).Nodup) (v : HS T Q A U) (S : Stacks T A) (ht : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (scanR src tmp (pushAll ks)) (mk v S)
      (4*(S.R src).length+4) (mk v' {S with R := fill ks (S.R src).length S.R}) := by
  obtain ⟨⟨hst,hs⟩,htmp,hd⟩ : (src ≠ tmp ∧ src ∉ ks) ∧ tmp ∉ ks ∧ ks.Nodup := by simpa using hr
  let Φ := fun (_ : Fin (A+4)) (R : Regs T A) => fill ks 1 R
  have hf : RegFx (pushAll (Q := Q) (U := U) ks) Φ :=
    fun _ p u M _ => ⟨u,rfl,push_run ks hd p u M⟩
  have frame {j : Fin T} (hj : j ∉ ks) : Frame j Φ := by
    intro x R l
    funext k
    by_cases h : k = j
    · subst k; simp [Φ,fill,hj]
    · simp [Φ,fill,h]
  obtain ⟨u,hu,he⟩ := scanR_exec' body hst hf (frame hs) (frame htmp) v S ht
  have iter (xs : List (Fin (A+4))) (R : Regs T A) :
      xs.foldl (fun R x => Φ x R) R = fill ks xs.length R := by
    induction xs generalizing R with
    | nil => funext k; simp [fill]
    | cons x xs ih =>
      rw [List.foldl_cons, ih]
      funext k
      by_cases h : k ∈ ks <;> simp [Φ,fill,h,List.replicate_succ',List.append_assoc]
  exact ⟨u,hu,by simpa only [iter] using he⟩

private theorem disjoint_counts (rs : List (Pair T)) (hd : (slots rs).Nodup)
    (p q : Pair T) (hp : p ∈ rs) (hq : q ∈ rs) : p.1 ≠ q.2 := by
  induction rs with
  | nil => simp at hp
  | cons a rs ih =>
    change (a.1 :: a.2 :: slots rs).Nodup at hd
    rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
    · exact fun h => hd.notMem (by simp [h])
    · exact fun h => hd.notMem (List.mem_cons_of_mem _ (h.symm ▸ List.mem_flatMap.mpr ⟨q,hq,by simp⟩))
    · exact fun h => hd.tail.notMem (h ▸ List.mem_flatMap.mpr ⟨p,(by assumption : p ∈ rs),by simp⟩)
    · exact ih hd.tail.tail hp hq

theorem filled_ready (rs : List (Pair T)) (hd : (slots rs).Nodup) (n : ℕ) (R : Regs T A)
    (hf : ∀ k ∈ slots rs, R k = []) :
    ready n (fill (rs.map Prod.fst) n R) rs := by
  intro r hr
  have h₁ := hf r.1 (List.mem_flatMap.mpr ⟨r,hr,by simp⟩)
  have h₂ := hf r.2 (List.mem_flatMap.mpr ⟨r,hr,by simp⟩)
  have hn : r.2 ∉ rs.map Prod.fst := fun h => by
    obtain ⟨p,hp,he⟩ := List.mem_map.mp h
    exact disjoint_counts rs hd p r hp hr he
  simp [fill,List.mem_map_of_mem hr,hn,h₁,h₂]

/-- Compute the high-part count once from the retained width, then initialize the traversal bank. -/
theorem prepare_exec (body : P → Pr P T Q A U) (rs : List (Pair T))
    (one width high tmp t₂ t₃ : Fin T)
    (hr : [one,width,high,tmp,t₂,t₃].Nodup)
    (hb : (high :: tmp :: slots rs).Nodup)
    (u : HS T Q A U) (S : Stacks T A) (w : ℕ) (hw : 0 < w)
    (hwidth : S.R width = List.replicate w tick) (h1 : (S.R one).length = 1)
    (hf : ∀ k ∈ [high,tmp,t₂,t₃] ++ slots rs, S.R k = []) :
    let H := prime^(w-1)
    let R := fill (rs.map Prod.fst) H (Function.update S.R high (List.replicate H tick))
    ready H R rs ∧ ∃ u' c, u'.user = u.user ∧ c ≤ 26*H+6 ∧
      Exec body (.seq (LabelCounts.highCount one width high tmp t₂ t₃)
        (scanR high tmp (pushAll (rs.map Prod.fst)))) (mk u S) c (mk u' {S with R := R}) := by
  let H := prime^(w-1)
  let M : Stacks T A := {S with R := Function.update S.R high (List.replicate H tick)}
  have hs (k) (hk : k ∈ slots rs) : k ≠ high := by
    intro e
    exact hb.notMem (List.mem_cons_of_mem _ (e ▸ hk))
  have fresh (k) (hk : k ∈ slots rs) : M.R k = [] := by
    simpa [M,hs k hk] using hf k (List.mem_append_right _ hk)
  refine ⟨filled_ready rs hb.tail.tail H M.R fresh, ?_⟩
  obtain ⟨v, c, hu, hc, he⟩ := LabelCounts.high_exec body hr u S w hw hwidth h1
    (fun k hk => hf k (List.mem_append_left _ hk))
  have sublist (ps : List (Pair T)) : List.Sublist (ps.map Prod.fst) (slots ps) := by
    induction ps with
    | nil => exact List.Sublist.slnil
    | cons r rs ih =>
      exact List.Sublist.cons_cons _ (List.Sublist.cons _ ih)
  have hd := (List.Sublist.cons_cons high (List.Sublist.cons_cons tmp (sublist rs))).nodup hb
  have hne : tmp ≠ high := fun e => hb.notMem (by simp [e])
  obtain ⟨z,hz,he'⟩ := copy_exec body high tmp _ hd v M (by simpa [M,hne] using hf tmp (by simp))
  have len : (M.R high).length = H := by simp [M]
  rw [len] at he'
  exact ⟨z, c+(4*H+4), hz.trans hu, by dsimp [H]; omega, Exec.seq he he'⟩

end
end IntegerMultBounds.MathlibTM2.Cover.LabelCountBank
