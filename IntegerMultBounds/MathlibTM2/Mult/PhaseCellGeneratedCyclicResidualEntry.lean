module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualIndexFromUnary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCyclicResidualEntry

/-! Read a selected physical residual row from ordinary geometry, retiring the private address. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generatedCyclicResidualEntry (rg : TblR 5 → Fin T)
    (header word saved tmp carry sPort aPort bPort iPort address width src dst
      skip savedSkip savedWord readTmp work₁ work₂ : Fin T) : Pr P T Q A U :=
  .seq (cyclicResidualIndexFromUnary rg header word saved tmp carry sPort aPort bPort iPort address)
    (.seq (copyIndexedWord address width src dst skip savedSkip savedWord readTmp work₁ work₂) (uclear address))

theorem generatedCyclicResidualEntry_exec (rg : TblR 5 → Fin T) (hrg : Function.Injective rg)
    (header word saved tmp carry sPort aPort bPort iPort address width src dst
      skip savedSkip savedWord readTmp work₁ work₂ : Fin T)
    (hheader : ∀ r, rg r ≠ header) (hoff : ∀ r, rg r ≠ address)
    (hregs : ∀ src ∈ [sPort,aPort,bPort,iPort], [src,rg .wr,word,saved,tmp,header].Nodup)
    (hread : [address,width,src,dst,skip,savedSkip,savedWord,readTmp,work₁,work₂].Nodup)
    {s : ℕ} [NeZero s] (W w a b : ℕ) (i : ZMod s) (ha : a ≤ s) (hb : b ≤ s) (hwide : s+s ≤ 2^W)
    (C D : ZMod s → GaussianInt) (tail wl : List (Fin (A+4))) (hwl : wl.length = W)
    (v : HS T Q A U) (S : Stacks T A)
    (hsSrc : (S.R sPort).length = s) (haSrc : (S.R aPort).length = a)
    (hbSrc : (S.R bPort).length = b) (hiSrc : (S.R iPort).length = i.val)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ r, r ≠ .wr → S.R (rg r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = []) (haddress : S.R address = [])
    (hw : (S.R width).length = w)
    (hsrc : S.R src = cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++tail))
    (hfresh : ∀ r ∈ [skip,savedSkip,savedWord,readTmp,work₁,work₂], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ unaryScalarResultCost S.R (cyclicResidualIndexInputs sPort aPort bPort iPort) W 3 (cyclicResidualIndex s a b i.val)+
        ((cyclicResidualIndex s a b i.val*(12*w+9)+10*w+22)+(2*cyclicResidualIndex s a b i.val+2)) ∧
      Exec body (generatedCyclicResidualEntry rg header word saved tmp carry sPort aPort bPort iPort address
        width src dst skip savedSkip savedWord readTmp work₁ work₂) (mk v S) m
        (mk v' {S with R := (Function.update S.R dst
          (csyms A w (if a ≤ i.val ∧ i.val < b then C i else D i)++S.R dst))}) := by
  have haddr (k : Fin T) (hk : k ∈ [width,src,dst,skip,savedSkip,savedWord,readTmp,work₁,work₂]) : k ≠ address := by
    intro he
    subst k
    exact (List.nodup_cons.mp hread).1 hk
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := cyclicResidualIndexFromUnary_exec (body := body) rg hrg
    header word saved tmp carry sPort aPort bPort iPort address hheader hoff hregs W s a b i.val ha hb i.val_lt hwide
    wl hwl v S hsSrc haSrc hbSrc hiSrc hwidth hblank hwork
  let F : Stacks T A := {S with R := Function.update S.R address (List.replicate (cyclicResidualIndex s a b i.val) tick)}
  have he₁' : Exec body (cyclicResidualIndexFromUnary rg header word saved tmp carry sPort aPort bPort iPort address)
      (mk v S) m₁ (mk v₁ F) := by simpa only [haddress,List.append_nil] using (he₁ 0).toExec
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := copyCyclicResidualEntry_exec (body := body) hread w a b i C D tail v₁ F
    (by simp [F]) (by simpa [F,haddr width (by simp)] using hw)
    (by simpa [F,haddr src (by simp)] using hsrc) (by
      intro k hk
      have hk' : k ∈ [width,src,dst,skip,savedSkip,savedWord,readTmp,work₁,work₂] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      simpa [F,haddr k hk'] using hfresh k hk)
  let xs := csyms A w (if a ≤ i.val ∧ i.val < b then C i else D i)++S.R dst
  let G : Stacks T A := {F with R := Function.update F.R dst xs}
  have he₂' : Exec body (copyIndexedWord address width src dst skip savedSkip savedWord readTmp work₁ work₂)
      (mk v₁ F) m₂ (mk v₂ G) := by simpa only [F,Function.update_of_ne (haddr dst (by simp))] using he₂
  obtain ⟨v₃,hv₃,he₃⟩ := uclear_exec body address v₂ G
  have hlen : (G.R address).length = cyclicResidualIndex s a b i.val := by
    simp [G,F,(haddr dst (by simp)).symm]
  refine ⟨v₃,m₁+(m₂+(2*cyclicResidualIndex s a b i.val+2)),hv₃.trans (hv₂.trans hv₁),by omega,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₃)
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k = address
    · subst k; simp [haddress,(haddr dst (by simp)).symm]
    · simp [G,F,xs,hk,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
