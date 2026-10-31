module

public import IntegerMultBounds.MathlibTM2.Host.EmbedInvariant
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Register placement replaces the selected stock and preserves spectator stock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main

private theorem sum_replace_embedding {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] (e : α → β) (he : Function.Injective e) (f g : β → ℕ) (h : α → ℕ)
    (hin : ∀ a, f (e a) = h a) (hoff : ∀ b, (¬ ∃ a, e a = b) → f b = g b) :
    (∑ b, f b)+(∑ a, g (e a)) = (∑ b, g b)+(∑ a, h a) := by
  classical
  let image : Finset β := Finset.univ.map ⟨e,he⟩
  have hfi : ∑ b ∈ image, f b = ∑ a, h a := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl (fun a _ => hin a)
  have hgi : ∑ b ∈ image, g b = ∑ a, g (e a) := by rw [Finset.sum_map]; rfl
  have hrest : ∑ b ∈ imageᶜ, f b = ∑ b ∈ imageᶜ, g b := by
    apply Finset.sum_congr rfl
    intro b hb
    apply hoff b
    intro ⟨a,ha⟩
    have hm : b ∈ image := Finset.mem_map.mpr ⟨a,Finset.mem_univ _,ha⟩
    exact (Finset.mem_compl.mp hb) hm
  have hf := Finset.sum_add_sum_compl image f
  have hg := Finset.sum_add_sum_compl image g
  omega

variable {T T' Q A : ℕ} {U : Type} (e : Fin T → Fin T')

theorem embK_injective (he : Function.Injective e) : Function.Injective (embK e) := by
  intro i j hij
  cases i <;> cases j <;> simp_all [embK,he.eq_iff]

/-- Exact stock balance for overwriting an embedded register bank. -/
theorem embOvr_stock (he : Function.Injective e)
    (f : ∀ k : HK T, List (HΓ A k)) (B : Stacks T' A) :
    (∑ k, ((embOvr e f B).get k).length)+(∑ k, ((embStk e B).get k).length) =
      (∑ k, (B.get k).length)+(∑ k, (f k).length) := by
  have hproj : (fun k : HK T => (B.get (embK e k)).length) =
      (fun k => ((embStk e B).get k).length) := by
    funext k
    cases k <;> rfl
  have h := sum_replace_embedding (embK e) (embK_injective e he)
    (fun k => ((embOvr e f B).get k).length) (fun k => (B.get k).length)
    (fun k => (f k).length) (fun k => by rw [embOvr_get he]; simp only [List.length_map]) (by
      intro k hk
      cases k with
      | inp => exact False.elim (hk ⟨.inp,rfl⟩)
      | out => exact False.elim (hk ⟨.out,rfl⟩)
      | lt j =>
        change (embExt e (fun i => f (.lt i)) B.L j).length = (B.L j).length
        rw [embExt_off]
        intro i hi
        exact hk ⟨.lt i,congrArg HK.lt hi⟩
      | rt j =>
        change (embExt e (fun i => f (.rt i)) B.R j).length = (B.R j).length
        rw [embExt_off]
        intro i hi
        exact hk ⟨.rt i,congrArg HK.rt hi⟩)
  simpa only [hproj] using h

/-- A boundary-stock allowance for a placed bank includes every spectator
stack exactly once through the surrounding initial state. -/
theorem embOvr_stock_le (he : Function.Injective e)
    (v : HS T Q A U) (w : HS T' Q A U) (S : Stacks T A) (B : Stacks T' A)
    (budget : ℕ)
    (hstock : mnSize (mk v S) ≤ mnSize (mk (embDn e w) (embStk e B))+budget) :
    mnSize (mk w (embOvr e S.get B)) ≤ mnSize (mk w B)+budget := by
  have hbalance := embOvr_stock e he S.get B
  change mnSize (mk w (embOvr e S.get B))+mnSize (mk (embDn e w) (embStk e B)) =
    mnSize (mk w B)+mnSize (mk v S) at hbalance
  omega

/-- A projected stock bound applies to a physical bank with the same
spectator stacks; callers need not manufacture an overwrite expression. -/
theorem projected_stock_le (he : Function.Injective e)
    (w : HS T' Q A U) (F B : Stacks T' A) (budget : ℕ)
    (hframe : ∀ j, (∀ i, e i ≠ j) → F.L j = B.L j ∧ F.R j = B.R j)
    (hstock : mnSize (mk (embDn e w) (embStk e F)) ≤
      mnSize (mk (embDn e w) (embStk e B))+budget) :
    mnSize (mk w F) ≤ mnSize (mk w B)+budget := by
  classical
  have hrestore : embOvr e (embStk e F).get B = F := by
    refine Stacks.ext rfl rfl ?_ ?_
    · funext j
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i,rfl⟩ := hj
        exact embExt_apply he _ _ i
      · exact (embOvr_off (embStk e F).get B (by simpa using hj)).1.trans
          (hframe j (by simpa using hj)).1.symm
    · funext j
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i,rfl⟩ := hj
        exact embExt_apply he _ _ i
      · exact (embOvr_off (embStk e F).get B (by simpa using hj)).2.trans
          (hframe j (by simpa using hj)).2.symm
  have hs := embOvr_stock_le e he (embDn e w) w (embStk e F) B budget hstock
  simpa only [hrestore] using hs

/-- An isolated loop counter may shrink before placing the next solver bank.
Its storage is already paid by the surrounding initial state. -/
theorem embOvr_stock_le_shrinking_counter (he : Function.Injective e)
    (v : HS T Q A U) (w : HS T' Q A U) (S : Stacks T A) (B : Stacks T' A)
    (count : Fin T') (hoff : ∀ i, e i ≠ count) (xs : List (Fin (A+4)))
    (hcount : xs.length ≤ (B.R count).length) (budget : ℕ)
    (hstock : mnSize (mk v S) ≤ mnSize (mk (embDn e w) (embStk e B))+budget) :
    mnSize (mk w (embOvr e S.get {B with R := Function.update B.R count xs})) ≤
      mnSize (mk w B)+budget := by
  have hp := embStk_updateR_off B count xs hoff
  have hb := embOvr_stock_le e he v w S
    {B with R := Function.update B.R count xs} budget (by simpa only [hp] using hstock)
  have hc := mn_size_update (mk w B) w (.rt count) xs
  have hbalance : mnSize (mk w {B with R := Function.update B.R count xs})+(B.R count).length =
      mnSize (mk w B)+xs.length := by
    simpa only [mk,update_rt,get_rt] using hc
  omega

/-- Lift a projected boundary bound to a physical state whose isolated counter
has shrunk. All other spectator stacks are retained exactly. -/
theorem projected_stock_le_shrinking_counter (he : Function.Injective e)
    (w : HS T' Q A U) (F B : Stacks T' A) (count : Fin T')
    (hoff : ∀ i, e i ≠ count) (budget : ℕ)
    (hframe : ∀ j, (∀ i, e i ≠ j) →
      F.L j = B.L j ∧ (j ≠ count → F.R j = B.R j))
    (hcount : (F.R count).length ≤ (B.R count).length)
    (hstock : mnSize (mk (embDn e w) (embStk e F)) ≤
      mnSize (mk (embDn e w) (embStk e B))+budget) :
    mnSize (mk w F) ≤ mnSize (mk w B)+budget := by
  let B' : Stacks T' A := {B with R := Function.update B.R count (F.R count)}
  have hp : embStk e B' = embStk e B := embStk_updateR_off B count (F.R count) hoff
  have hs := projected_stock_le e he w F B' budget (by
    intro j hj
    refine ⟨(hframe j hj).1,?_⟩
    by_cases hc : j = count
    · subst j; simp [B']
    · simpa only [B',Function.update_of_ne hc] using (hframe j hj).2 hc)
    (by simpa only [hp] using hstock)
  have hbalance : mnSize (mk w B')+(B.R count).length =
      mnSize (mk w B)+(F.R count).length := by
    simpa only [B',mk,update_rt,get_rt] using mn_size_update (mk w B) w (.rt count) (F.R count)
  omega

theorem embAct_push (a : Act T Q A U) : mnActPush (embAct e a) = mnActPush a := by
  induction a <;> simp_all [embAct,mnActPush]

theorem embProg_push {P P' : Type} (ι : P → P') (p : Pr P T Q A U) :
    mnProgPush (embProg e ι p) = mnProgPush p := by
  induction p <;> simp_all [embProg,mnProgPush,embAct_push]

/-- Register placement preserves a call-free atomic push certificate. -/
theorem embProg_native {P P' : Type} {c : ℕ} (ι : P → P') (p : Pr P T Q A U)
    (h : mnNativePushBound c p) : mnNativePushBound c (embProg e ι p) := by
  induction p with
  | act a => simpa only [embProg,mnNativePushBound,embAct_push] using h
  | seq p q hp hq => exact ⟨hp h.1,hq h.2⟩
  | cond f p q hp hq => exact ⟨hp h.1,hq h.2⟩
  | loop f p hp => exact hp h
  | call f => exact False.elim h

/-- Place a proved stock certificate over an arbitrary background, counting all
spectator stacks in the big initial stock exactly once. -/
theorem exec_emb_ovr_within_stock {P P' : Type} {ι : P → P'}
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
    (he : Function.Injective e) (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
    {p : Pr P T Q A U} {v v₁ : HS T Q A U} {S S₁ : Stacks T A}
    {steps depth budget : ℕ}
    (hex : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+budget)
      depth p (mk v S) steps (mk v₁ S₁))
    (w : HS T' Q A U) (hw : embDn e w = v) (B : Stacks T' A) (hB : embStk e B = S) :
    ∃ w', embDn e w' = v₁ ∧ w'.user = v₁.user ∧
      ExecWithin body' (fun d z => mnSize z+d ≤ mnSize (mk w B)+depth+budget)
        depth (embProg e ι p) (mk w B) steps (mk w' (embOvr e S₁.get B)) := by
  have hInv : ∀ d z (wi : HS T' Q A U), embDn e wi = z.var →
      mnSize z+d ≤ mnSize (mk v S)+depth+budget →
      mnSize (⟨wi,(embOvr e z.stk B).get⟩ : Store (HΓ (T := T') A) (HS T' Q A U))+d ≤
        mnSize (mk w B)+depth+budget := by
    intro d z wi _ hz
    have hsize : mnSize (⟨wi,(embOvr e z.stk B).get⟩ : Store (HΓ (T := T') A) (HS T' Q A U))+
        mnSize (mk v S) = mnSize (mk w B)+mnSize z := by
      rw [← hB]
      exact embOvr_stock e he z.stk B
    omega
  obtain ⟨wf,hwf,ht⟩ := embProg_execWithin he hbody B
    (J := fun d z => mnSize z+d ≤ mnSize (mk w B)+depth+budget) hInv hex w hw
  have hstart : embOvr e (mk v S).stk B = B := by
    rw [mk_stk,← hB]
    exact embOvr_stk B
  rw [hstart] at ht
  have hwf' : embDn e wf = v₁ := hwf
  exact ⟨wf,hwf',by rw [← hwf']; rfl,ht⟩

/-- Stock-aware counterpart of `exec_emb`: keep the projected final bank and
external frame alongside the simultaneous stock certificate. The allowance is
relative to the whole initial bank, so spectator storage is counted once. -/
theorem exec_emb_within_stock {P P' : Type} {ι : P → P'}
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
    (he : Function.Injective e) (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
    {p : Pr P T Q A U} {v v₁ : HS T Q A U} {S S₁ : Stacks T A}
    {steps depth budget : ℕ}
    (hex : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+budget)
      depth p (mk v S) steps (mk v₁ S₁))
    (w : HS T' Q A U) (hw : embDn e w = v) (B : Stacks T' A) (hB : embStk e B = S) :
    ∃ w' G, embDn e w' = v₁ ∧ w'.user = v₁.user ∧
      ExecWithin body' (fun d z => mnSize z+d ≤ mnSize (mk w B)+depth+budget)
        depth (embProg e ι p) (mk w B) steps (mk w' G) ∧
      embStk e G = S₁ ∧
      ∀ j, (∀ i, e i ≠ j) → G.L j = B.L j ∧ G.R j = B.R j := by
  obtain ⟨w',hw',hu,ht⟩ := exec_emb_ovr_within_stock e he hbody hex w hw B hB
  exact ⟨w',embOvr e S₁.get B,hw',hu,ht,embStk_ovr he S₁ B,
    fun j hj => embOvr_off S₁.get B hj⟩

end IntegerMultBounds.MathlibTM2.Host
