module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadCyclicSeedEndpoints
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGeneratedHeaders

/-! Structural composition of an origin reader, a consuming callback and
endpoint retirement. The callback's certificate and reserve are preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicSeedLayout
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def readRunRetire (g : CyclicSeedLayout T) (width halo origins binary work saved tmp : Fin T)
    (run : Pr P T Q A U) : Pr P T Q A U :=
  .seq (readSupplierEndpoints width halo origins binary (g.source 6) (g.source 7) work saved tmp)
    (.seq run (clearWords [g.source 6,g.source 7]))

theorem readRunRetire_exec (g : CyclicSeedLayout T)
    (width halo origins binary work saved tmp archive dst : Fin T)
    (hreg : [width,halo,origins,binary,g.source 6,g.source 7,work,saved,tmp].Nodup)
    (hoff : ∀ k, g.retained k → origins ≠ k ∧ g.source 6 ≠ k ∧ g.source 7 ≠ k)
    (harchive : archive ≠ g.source 6 ∧ archive ≠ g.source 7)
    (hdst : dst ≠ origins ∧ dst ≠ g.source 6 ∧ dst ≠ g.source 7)
    {B p u l target s t a n W N V : ℕ} (hfit : a < 2^V)
    (originTail tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (ready : g.Ready B p u l target s t 0 0 W N S)
    (hwidth : (S.R width).length = V) (hhalo : (S.R halo).length = n)
    (horigins : S.R origins = binSyms V a++originTail)
    (hblank : ∀ k ∈ [binary,g.source 6,g.source 7,work,saved,tmp], S.R k = [])
    (run : Pr P T Q A U) (Cert : ℕ → ℕ → List (Fin (A+4)) → Prop)
    (hrun : ∀ (vi : HS T Q A U) (E : Stacks T A),
      E = {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
        (g.source 6) (List.replicate a tick)) (g.source 7) (List.replicate (a+n) tick))} →
      g.Ready B p u l target s t a n W N E →
      ∃ vm steps word runTime reserve, vm.user = vi.user ∧ steps ≤ runTime ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk vi E)+0+reserve) 0
          run (Host.mk vi E) steps
          (Host.mk vm {E with R := Function.update (Function.update E.R archive tail) dst (word++E.R dst)}) ∧
        Cert runTime reserve word) :
    ∃ v' steps word runTime reserve, v'.user = v.user ∧
      steps ≤ readSupplierEndpointsCost V a n+runTime+(2*(a+(a+n))+5) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        (3*readSupplierEndpointsCost V a n+reserve)) 0
        (g.readRunRetire width halo origins binary work saved tmp run) (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
          archive tail) dst (word++S.R dst))}) ∧ Cert runTime reserve word := by
  let E : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
    (g.source 6) (List.replicate a tick)) (g.source 7) (List.replicate (a+n) tick))}
  obtain ⟨vi,m,hui,hm,heRead,hready⟩ := read_endpoints_exec (body := body) g width halo origins binary work saved tmp
    hreg hoff hfit originTail v S ready hwidth hhalo horigins hblank
  obtain ⟨vm,k,word,runTime,reserve,hum,hk,heRun,hcert⟩ := hrun vi E rfl hready
  let D : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
    archive tail) dst (word++S.R dst))}
  let F : Stacks T A := {E with R := Function.update (Function.update E.R archive tail) dst (word++E.R dst)}
  let ports : Fin 2 → Fin T := ![g.source 6,g.source 7]
  let values : Fin 2 → ℕ := ![a,a+n]
  have hsep : g.source 6 ≠ g.source 7 := by
    have hr := hreg; regs_ne hr; assumption
  have ho6 : origins ≠ g.source 6 := by
    have hr := hreg; regs_ne hr; assumption
  have ho7 : origins ≠ g.source 7 := by
    have hr := hreg; regs_ne hr; assumption
  have hinj : Function.Injective ports := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [ports,hsep,Ne.symm hsep] at hij ⊢
  have hb6 := hblank (g.source 6) (by simp)
  have hb7 := hblank (g.source 7) (by simp)
  have hD (i : Fin 2) : D.R (ports i) = [] := by
    fin_cases i <;> simp [D,ports,Ne.symm harchive.1,Ne.symm harchive.2,Ne.symm hdst.2.1,Ne.symm hdst.2.2,Ne.symm ho6,Ne.symm ho7,hb6,hb7]
  have hvalues (i : Fin 2) : (F.R (ports i)).length = values i := by
    fin_cases i <;> simp [F,E,ports,values,Ne.symm harchive.1,Ne.symm harchive.2,Ne.symm hdst.2.1,Ne.symm hdst.2.2,hsep]
  have hframe (r : Fin T) (h : ∀ i, ports i ≠ r) : F.R r = D.R r := by
    have h6 := h 0
    have h7 := h 1
    simp only [ports,Matrix.cons_val_zero,Matrix.cons_val_one] at h6 h7
    by_cases hd : r = dst
    · subst r
      simp [F,D,E,hdst.1,hdst.2.1,hdst.2.2]
    · by_cases ha : r = archive
      · subst r
        simp [F,D,E,hd]
      · simp [F,D,E,hd,ha,Ne.symm h6,Ne.symm h7,hdst.1,hdst.2.1,hdst.2.2]

  obtain ⟨vf,huf,heClear⟩ := retireGeneratedHeaders_exec (body := body) ports hinj values vm D F
    hD hvalues rfl rfl rfl hframe 0
  have heClear' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk vm F)+0) 0
      (clearWords [g.source 6,g.source 7]) (Host.mk vm F) (2*(a+(a+n))+5) (Host.mk vf D) := by
    simpa [ports,values,List.ofFn_succ] using heClear
  have hrunClear := ExecWithin.seq heRun (heClear'.mono (by
    intro d z hz
    have hp := heRun.final
    change mnSize (Host.mk vm F)+0 ≤ _ at hp
    omega))
  have hwhole := execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ heRead hrunClear
  refine ⟨vf,m+(k+(2*(a+(a+n))+5)),word,runTime,reserve,huf.trans (hum.trans hui),?_,hwhole,hcert⟩
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicSeedLayout
