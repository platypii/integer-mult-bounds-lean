module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalDescriptor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompletedGatheredFeedCouplingInterval

/-! One interval step consumes its binary descriptor, reuses shared geometry and
coefficient data, and releases all dynamic metadata before the next interval. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

noncomputable def descriptorCouplingInterval (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 168 Q A U :=
  .seq loadCouplingIntervalDescriptor
    (.seq (completedGatheredFeedCouplingInterval hQ boundary) releaseCouplingIntervalDescriptor)

theorem descriptorCouplingInterval_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hsource : S.R 160 = cstream A w (rawCouplingRibbon band origin N C)++tail)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin N)++pageTail)
    (hindex : (S.R 107).length = origin) (hrhs : S.R 93 = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R 143 = [])
    (hxs : ∀ j < N, ∀ x ∈ couplingInputWords boundary t band a b (origin+j) C, Fits w x)
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin N).length)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hfitV : origin+(N+2*band)+s < 2^V)
    (hV : (S.R 163).length = V)
    (hshared : ∀ k ∈ [(145 : Fin 168),146,147,149,151],
      S.R k = binSyms V (couplingIntervalValue s t band a b origin N k))
    (hblank : ∀ k ∈ [(148 : Fin 168),154,155,156,164,165], S.R k = [])
    (descriptorTail : List (Fin (A+4)))
    (hpacket : S.R 159 = binSyms V origin++binSyms V N++descriptorTail)
    (h158 : S.R 158 = []) (h135 : S.R 135 = []) (h167 : S.R 167 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (36*V+36+(((8*N+8*band+11*V+12+(152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72)+maskCouplingSourceCost (N+2*band) w)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        (144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26)))+24*V+25 ∧
      Exec body (descriptorCouplingInterval hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 159 descriptorTail) 93 rhsTail) 110
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++S.R 110))}) := by
  have h0 : S.R 0 = [] := hready.low 0 (by decide)
  have h1 : S.R 1 = [] := hready.low 1 (by decide)
  obtain ⟨v₁,hu₁,he₁⟩ := loadCouplingIntervalDescriptor_exec (body := body) V origin N descriptorTail v S
    hV hpacket (hblank 155 (by simp)) (hblank 165 (by simp)) h0 h1
  let L : Stacks 168 A := {S with R := (Function.update (Function.update (Function.update S.R 159 descriptorTail)
    155 (binSyms V origin)) 165 (binSyms V N))}
  have hbase : ∀ k ∈ [(145 : Fin 168),146,147,149,151,155,165],
      L.R k = binSyms V (couplingIntervalValue s t band a b origin N k) := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [L] using hshared 145 (by simp)
    · simpa [L] using hshared 146 (by simp)
    · simpa [L] using hshared 147 (by simp)
    · simpa [L] using hshared 149 (by simp)
    · simpa [L] using hshared 151 (by simp)
    · simp [L,couplingIntervalValue]
    · simp [L,couplingIntervalValue]
  have hproj : embStk groupReg (embStk intervalPageReg L) = embStk groupReg (embStk intervalPageReg S) := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hk := k.isLt
    have hn155 : k.val ≠ 155 := by omega
    have hn159 : k.val ≠ 159 := by omega
    have hn165 : k.val ≠ 165 := by omega
    simp [L,embStk,groupReg,intervalPageReg,Fin.ext_iff,hn155,hn159,hn165]
  have hreadyL : RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg L)) := by rw [hproj]; exact hready
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := completedGatheredFeedCouplingInterval_exec (body := body)
    hQ boundary hA hw5 hqw hst C B hfit tail pageTail rhsTail raw v₁ L hreadyL
    (by simpa [L] using hsource) (by simpa [L] using hrows) (by simpa [L] using hpage)
    (by simpa [L] using hindex) (by simpa [L] using hrhs) (by simpa [L] using h143)
    hxs has V (by simpa [L] using h166) (by simpa [L] using h139)
    haS hbS hbandS hwide hfitV (by simpa [L] using hV) hbase
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;>
          simpa [L] using hblank _ (by simp))
    (by simpa [L] using h158) (by simpa [L] using h135) (by simpa [L] using h167)
  let F : Stacks 168 A := {L with R := (Function.update
    (Function.update (completedCouplingIntervalR L.R V band origin N) 93 rhsTail) 110
    (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B))++L.R 110))}
  have hfields : ∀ k ∈ [(148 : Fin 168),154,155,156,164,165], (F.R k).length = V := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [F,L,completedCouplingIntervalR]
  obtain ⟨v₃,hu₃,he₃⟩ := releaseCouplingIntervalDescriptor_exec (body := body) V v₂ F hfields
  refine ⟨v₃,(12*V+12)+(m₂+(12*V+13)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hm : k ∈ [(148 : Fin 168),154,155,156,164,165]
  · have hb := hblank k hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hb]
  · have hn := hm
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    by_cases h93 : k = 93 <;> by_cases h110 : k = 110 <;> by_cases h159 : k = 159 <;>
      simp [F,L,completedCouplingIntervalR,hm,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,
        hn.2.2.2.2.1,hn.2.2.2.2.2,h93,h110,h159]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
