module

public import IntegerMultBounds.MathlibTM2.Host.Placed
public import IntegerMultBounds.MathlibTM2.Host.ForeignWithin
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Preserve the existing idle-frame and endpoint contracts while adding the
bounded simulator trace. Determinism joins the two certificates for one run. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

theorem foreign_exec_frame_within (M : Program T Q A) (body : P → Pr P T Q A U)
    {I : Fin T → Prop} (hI : Idle M I) {pre post : TapePred T A} {k : ℕ}
    (lo upper : ℤ)
    (h : HoareWithin M pre post k (fun z => ∀ i, lo ≤ z.head i ∧ z.head i ≤ upper))
    (v : HS T Q A U) (S : Stacks T A) (w : Tapes T A) (hw : pre w)
    (hrep : RepT w S.L S.R) (depth : ℕ) :
    ∃ v' S' w', post w' ∧ RepT w' S'.L S'.R ∧ v'.user = v.user ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      (∀ i, (S'.L i).length+(S'.R i).length ≤ (S.L i).length+(S.R i).length+2*k) ∧
      (∀ i, I i → S'.L i = S.L i ∧ (S'.R i = S.R i ∨ S'.R i = padR (S.R i))) ∧
      ∃ m ≤ k*(T+5)+6,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+
          T*(upper+1-lo).toNat+depth+2*(T+4)) depth
          (foreign M) (mk v S) m (mk v' S') := by
  obtain ⟨v',S',w',hp,hr,hu,hin,hout,hlen,hframe,m,hm,he⟩ :=
    foreign_exec_frame body M hI h.time v S w hw hrep
  obtain ⟨vf,Sf,wf,hpf,hrf,huf,hinf,houtf,n,hn,ht⟩ :=
    foreign_exec_within_hoare_heads M body lo upper h v S w hw hrep depth
  obtain ⟨hsteps,hfinal⟩ := ht.toExec.unique he
  rw [hsteps,hfinal] at ht
  exact ⟨v',S',w',hp,hr,hu,hin,hout,hlen,hframe,m,hm,ht⟩

end IntegerMultBounds.MathlibTM2.Host
