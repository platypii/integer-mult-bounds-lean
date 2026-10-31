module

public import IntegerMultBounds.MathlibTM2.Host.ForeignHeadStock
public import IntegerMultBounds.Machine.HoareWithin

/-! A bounded machine contract supplies the reachable invariant of its actual
host simulation, so callers only account for their initial represented stacks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

private theorem interval_storage (lo upper : ℤ) (l r : ℕ) :
    (upper+(r : ℕ)+1-(lo-(l : ℕ))).toNat ≤ l+r+(upper+1-lo).toNat := by omega

theorem foreign_exec_within_hoare_heads (M : Program T Q A) (body : P → Pr P T Q A U)
    {pre post : TapePred T A} {k : ℕ} (lo upper : ℤ)
    (h : HoareWithin M pre post k (fun z => ∀ i, lo ≤ z.head i ∧ z.head i ≤ upper))
    (v : HS T Q A U) (S : Stacks T A) (w : Tapes T A) (hw : pre w)
    (hrep : RepT w S.L S.R) (depth : ℕ) :
    ∃ v' S' w', post w' ∧ RepT w' S'.L S'.R ∧ v'.user = v.user ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ ∃ m ≤ k*(T+5)+6,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+
        T*(upper+1-lo).toNat+depth+2*(T+4)) depth
        (foreign M) (mk v S) m (mk v' S') := by
  let left := fun i => lo-((S.L i).length : ℤ)
  let right := fun i => upper+((S.R i).length : ℤ)
  have hheads : ∀ c, RunInvariant M pre c → ∀ i, left i ≤ c.head i ∧ c.head i ≤ right i := by
    intro c hc i
    have hh := h.invariant hc i
    change lo ≤ c.head i ∧ c.head i ≤ upper at hh
    dsimp only [left,right]
    omega
  have hspan : StackSpan left right (w.start M) S := by
    intro i
    have hh := h.invariant (RunInvariant.initial hw) i
    change lo ≤ w.head i ∧ w.head i ≤ upper at hh
    dsimp only [left,right,Tapes.start]
    omega
  obtain ⟨v',S',w',hp,hr,hu,hin,hout,m,hm,he⟩ :=
    foreign_exec_within_head_bounds M body h.time (RunInvariant M pre)
      left right hheads (fun c c' hc hs => hc.step hs)
      v S w hw hrep (RunInvariant.initial hw) hspan depth
  have hstorage : (∑ i, (right i+1-left i).toNat) ≤
      registerBankStock S+T*(upper+1-lo).toNat := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => interval_storage lo upper (S.L i).length (S.R i).length)
    simpa only [left,right,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,registerBankStock,Finset.sum_add_distrib] using hsum
  refine ⟨v',S',w',hp,hr,hu,hin,hout,m,hm,he.mono ?_⟩
  intro d z hz
  rw [mnSize_mk_registerBankStock]
  omega

end IntegerMultBounds.MathlibTM2.Host
