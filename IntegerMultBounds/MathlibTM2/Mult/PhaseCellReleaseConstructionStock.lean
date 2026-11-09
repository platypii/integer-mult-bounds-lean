module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseConstruction
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Construction retirement charges native traffic, independently of numerical iteration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem releaseConstruction_native :
    mnNativePushBound 3 (releaseConstruction (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [releaseConstruction,releaseFactorPage,releaseFromDimensions,releasePrefix,
    clearWords,unaryProduct,transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,popDo,
    keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem releaseConstruction_exec_within (P s t u band L q W n : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L) (hwidth : (S.R 94).length = W)
    (hblank : ∀ r, S.R (cr r) = []) (hiteration : S.R 116 = [])
    (hfresh : ∀ k ∈ [(97 : Fin 117), 99, 104, 105, 106], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseConstructionCost L W n ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤
          mnSize (mk v (packedGeneratorBank (constructedFactorBank S P s t u band L W)
            P s t u band L q W n))+depth+3*releaseConstructionCost L W n)
        depth releaseConstruction
        (mk v (packedGeneratorBank (constructedFactorBank S P s t u band L W) P s t u band L q W n)) m
        (mk v' (retainedGeneratorBank S P s t u band L q n))) := by
  obtain ⟨v',m,hu,hm,he⟩ := releaseConstruction_exec (body := body)
    P s t u band L q W n v S hrows hcount hwidth hblank hiteration hfresh
  refine ⟨v',m,hu,hm,?_⟩
  intro depth
  exact mn_native_exec_within he 3 releaseConstruction_native depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
