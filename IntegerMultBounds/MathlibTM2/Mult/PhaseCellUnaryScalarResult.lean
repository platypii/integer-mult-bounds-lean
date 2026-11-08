module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallUnaryScalarInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarHeaderStock
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Run scalar arithmetic from ordinary unary inputs and export one result, retiring its bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def unaryScalarInputState (ports : List (Fin n × Fin T)) (R : Regs T A) : TblSt n A :=
  loadedBinaryState (ports.map (fun p => (p.1,(R p.2).length))) ⟨fun _ => 0,[]⟩

def unaryScalarResult (rg : TblR n → Fin T) (header word saved tmp carry : Fin T)
    (ports : List (Fin n × Fin T)) (code : TblCode n) (result : Fin n) (dst : Fin T) : Pr P T Q A U :=
  .seq (installUnaryScalarInputs rg header word saved tmp carry ports)
    (.seq (tblCompile rg code) (.seq (tblUnaryCopies rg [(result,dst)]) (releaseScalarBank rg)))

def unaryScalarResultCost (R : Regs T A) (ports : List (Fin n × Fin T)) (W atoms value : ℕ) : ℕ :=
  (binaryHeaderQueueCost R W (ports.map Prod.snd)+n*(4*W+4)+ports.length*(8*W+8)+2)+
    (atoms*tblC W 0+((6*value+11*W+7)+(2*(n*W)+2*n+1)))

theorem unaryScalarResult_native (rg : TblR n → Fin T) (header word saved tmp carry : Fin T)
    (ports : List (Fin n × Fin T)) (code : TblCode n) (result : Fin n) (dst : Fin T) :
    mnNativePushBound 3 (unaryScalarResult (P := P) (Q := Q) (A := A) (U := U)
      rg header word saved tmp carry ports code result dst) :=
  ⟨installUnaryScalarInputs_native ..,tblCompile_native ..,
    mnNativePushBound_mono (by decide) (tblUnaryCopies_native ..),
    mnNativePushBound_mono (by decide : 0 ≤ 3) (clearWords_native _)⟩

theorem unaryScalarResult_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (header word saved tmp carry : Fin T) (hheader : ∀ r, rg r ≠ header)
    (ports : List (Fin n × Fin T))
    (hregs : ∀ src ∈ ports.map Prod.snd, [src,rg .wr,word,saved,tmp,header].Nodup)
    (code : TblCode n) (result : Fin n) (dst : Fin T) (hoff : ∀ r, rg r ≠ dst)
    (W atoms value : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (v : HS T Q A U) (S : Stacks T A) (hwidth : S.R (rg .wr) = wl)
    (hblank : ∀ r, r ≠ .wr → S.R (rg r) = []) (hwork : ∀ k ∈ [word,saved,tmp], S.R k = [])
    (hfit : ∀ i, (unaryScalarInputState ports S.R).val i < 2^W)
    (hcode : TblDo A W 0 code (unaryScalarInputState ports S.R)
      (fun F => F.val result = value ∧ F.acc = [] ∧ ∀ i, F.val i < 2^W) atoms) :
    ∃ v' m, v'.user = v.user ∧ m ≤ unaryScalarResultCost S.R ports W atoms value ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        3*unaryScalarResultCost S.R ports W atoms value) depth
        (unaryScalarResult rg header word saved tmp carry ports code result dst) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (List.replicate value tick++S.R dst)}) := by
  obtain ⟨v₁,M,m₁,hv₁,hm₁,he₁,hh₁,hin₁,hout₁,hL₁,hframe₁⟩ := installUnaryScalarInputs_exec (body := body)
    rg hrg header word saved tmp carry hheader ports hregs W wl hwl v S hwidth hblank hwork
  obtain ⟨st,hpost,hrun⟩ := TblDo.host (body := body) hrg wl [] hwl rfl (by omega : 0 ≤ W) hcode hfit
  obtain ⟨v₂,M₂,m₂,hv₂,hm₂,he₂,hh₂,hin₂,hout₂,hL₂,hframe₂⟩ := hrun v₁ M hh₁
  change m₂ ≤ atoms*tblC W 0 at hm₂
  rcases hpost with ⟨hvalue,hacc,hfit₂⟩
  obtain ⟨v₃,m₃,hv₃,hm₃,he₃⟩ := tblUnaryCopies_exec (body := body) hrg wl [] st hfit₂
    [(result,dst)] (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact hoff) v₂ M₂ hh₂
  let F : Stacks T A := {M₂ with R := Function.update M₂.R dst (List.replicate value tick++M₂.R dst)}
  let G : Stacks T A := {S with R := Function.update S.R dst (List.replicate value tick++S.R dst)}
  have he₃' : Exec body (tblUnaryCopies rg [(result,dst)]) (mk v₂ M₂) m₃ (mk v₃ F) := by
    simpa only [unaryCopiesR,hvalue] using he₃
  have hhF : tblHolds rg F (tblRho W wl [] st) := by
    intro r
    exact (Function.update_of_ne (hoff r) _ _).trans (hh₂ r)
  have hframe (k : Fin T) (hk : ∀ r, rg r ≠ k) : M₂.R k = S.R k :=
    (hframe₂ k hk).trans (hframe₁ k hk)
  have hbase (k : Fin T) (hk : ∀ r, rg r ≠ k) : F.R k = G.R k := by
    by_cases hdst : k = dst
    · subst k; simp [F,G,hframe dst hoff]
    · simpa only [F,G,Function.update_of_ne hdst] using hframe k hk
  obtain ⟨v₄,hv₄,he₄⟩ := releaseScalarBank_to_state_exec (body := body) rg hrg W wl st hacc v₃ F G hhF
    ((Function.update_of_ne (hoff .wr) _ _).trans hwidth)
    (fun r hr => (Function.update_of_ne (hoff r) _ _).trans (hblank r hr))
    (hin₂.trans hin₁) (hout₂.trans hout₁) (hL₂.trans hL₁) hbase
  have hconvert : m₃ ≤ 6*value+11*W+7 := by
    simpa only [unaryCopiesCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hvalue,Nat.add_zero] using hm₃
  have hex : Exec body (unaryScalarResult rg header word saved tmp carry ports code result dst)
      (mk v S) (m₁+(m₂+(m₃+(2*(n*W)+2*n+1)))) (mk v₄ G) :=
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))
  have hcost : m₁+(m₂+(m₃+(2*(n*W)+2*n+1))) ≤ unaryScalarResultCost S.R ports W atoms value := by
    dsimp only [unaryScalarResultCost]
    omega
  exact ⟨v₄,_,hv₄.trans (hv₃.trans (hv₂.trans hv₁)),hcost,fun depth =>
    mn_native_exec_within hex 3 (unaryScalarResult_native ..) depth
      (mnSize (mk v S)+depth+3*unaryScalarResultCost S.R ports W atoms value) (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
