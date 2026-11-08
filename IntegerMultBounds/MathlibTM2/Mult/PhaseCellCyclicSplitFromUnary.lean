module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSplitCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallUnaryScalarInputs

/-! Execute cyclic endpoint arithmetic from retained unary dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def cyclicSplitInputs (sPort aPort nPort : Fin T) : List (Fin 7 × Fin T) :=
  [(0,sPort),(1,aPort),(2,nPort)]

def cyclicSplitFromUnary (rg : TblR 7 → Fin T) (header word saved tmp carry sPort aPort nPort : Fin T) : Pr P T Q A U :=
  .seq (installUnaryScalarInputs rg header word saved tmp carry (cyclicSplitInputs sPort aPort nPort))
    (tblCompile rg cyclicSplitCode)

theorem cyclicSplitFromUnary_exec (rg : TblR 7 → Fin T) (hrg : Function.Injective rg)
    (header word saved tmp carry sPort aPort nPort : Fin T) (hheader : ∀ r, rg r ≠ header)
    (hregs : ∀ src ∈ [sPort,aPort,nPort], [src,rg .wr,word,saved,tmp,header].Nodup)
    (W s a n : ℕ) (has : a ≤ s) (hns : n ≤ s) (hwide : s < 2^W)
    (wl : List (Fin (A+4))) (hwl : wl.length = W) (v : HS T Q A U) (S : Stacks T A)
    (hs : (S.R sPort).length = s) (ha : (S.R aPort).length = a) (hn : (S.R nPort).length = n)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ r, r ≠ .wr → S.R (rg r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = []) :
    ∃ v' F steps st, v'.user = v.user ∧
      steps ≤ binaryHeaderQueueCost S.R W [sPort,aPort,nPort]+7*(4*W+4)+3*(8*W+8)+2+5*tblC W 0 ∧
      Exec body (cyclicSplitFromUnary rg header word saved tmp carry sPort aPort nPort) (mk v S) steps (mk v' F) ∧
      tblHolds rg F (tblRho W wl [] st) ∧ st.val 5 = a+min n (s-a) ∧ st.val 6 = n-min n (s-a) ∧
      st.val 0 = s ∧ st.val 1 = a ∧ st.val 2 = n ∧ st.acc = [] ∧
      (∀ i, st.val i < 2^W) ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ k, (∀ r, rg r ≠ k) → F.R k = S.R k) := by
  obtain ⟨v₁,M,m₁,hv₁,hm₁,he₁,hh,hin,hout,hL,hframe⟩ := installUnaryScalarInputs_exec
    (body := body) rg hrg header word saved tmp carry hheader (cyclicSplitInputs sPort aPort nPort)
    (by simpa only [cyclicSplitInputs,List.map_cons,List.map_nil] using hregs) W wl hwl v S hwidth hblank hwork
  have hinputs : (cyclicSplitInputs sPort aPort nPort).map (fun a => (a.1,(S.R a.2).length)) = [(0,s),(1,a),(2,n)] := by
    simp only [cyclicSplitInputs,List.map_cons,List.map_nil,hs,ha,hn]
  rw [hinputs] at hh
  let st : TblSt 7 A := loadedBinaryState [(0,s),(1,a),(2,n)] ⟨fun _ => 0,[]⟩
  have hvals : st.val 0 = s ∧ st.val 1 = a ∧ st.val 2 = n ∧ st.acc = [] := by simp [st,loadedBinaryState]
  have hfit : ∀ i, st.val i < 2^W := by
    intro i
    simp only [st,loadedBinaryState,Function.update_apply]
    split_ifs <;> omega
  obtain ⟨st',hpost,hrun⟩ := TblDo.host (body := body) hrg wl [] hwl rfl (by omega : 0 ≤ W)
    (cyclicSplitCode_do st hvals.1 hvals.2.1 hvals.2.2.1 has hns hwide) hfit
  obtain ⟨v₂,F,m₂,hv₂,hm₂,he₂,hh₂,hi₂,ho₂,hl₂,hf₂⟩ := hrun v₁ M hh
  change m₂ ≤ 5*tblC W 0 at hm₂
  rcases hpost with ⟨hend,hrest,hroom,hmin,hacc,hkeep⟩
  have hinput (i : Fin 7) (hi : i ∉ [(3 : Fin 7),4,5,6]) : st'.val i = st.val i := hkeep i hi
  have hfits : ∀ i, st'.val i < 2^W := by
    intro i
    by_cases h3 : i = 3
    · subst i; rw [hroom]; omega
    by_cases h4 : i = 4
    · subst i; rw [hmin]; omega
    by_cases h5 : i = 5
    · subst i; rw [hend]; omega
    by_cases h6 : i = 6
    · subst i; rw [hrest]; omega
    rw [hkeep i (by simp [h3,h4,h5,h6])]
    exact hfit i
  refine ⟨v₂,F,m₁+m₂,st',hv₂.trans hv₁,?_,Exec.seq he₁ he₂,hh₂,hend,hrest,
    (hinput 0 (by decide)).trans hvals.1,(hinput 1 (by decide)).trans hvals.2.1,
    (hinput 2 (by decide)).trans hvals.2.2.1,hacc.trans hvals.2.2.2,hfits,
    hi₂.trans hin,ho₂.trans hout,hl₂.trans hL,?_⟩
  · simp only [cyclicSplitInputs,List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hm₁
    omega
  · intro k hk
    exact (hf₂ k hk).trans (hframe k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
