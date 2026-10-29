module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSavedHeaders

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def packedProtectedCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  withSavedHeaders [105,106] (protectedCouplingRow hQ)

theorem packedProtectedCouplingRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w) (hq : (S.R 112).length = q)
    (hx : S.R 110 = cstream A w xs++tailX) (ha : S.R 111 = cstream A w as++tailA)
    (hrhs : S.R 93 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hblank : ∀ r : CR, S.R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], S.L k = [])
    (hwork : ∀ k ∈ integerRowWork, k ∉ [(97 : Fin 117),98,99,105,106] → S.R k = [])
    (h109 : S.R 109 = [])
    (hmetaLeft : ∀ r ∈ [(105 : Fin 117),106], S.L r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ generatedReadyRowCost L q w (S.R 100).length+
        4*((S.R 97).length+(S.R 98).length+(S.R 99).length)+12+
        4*(S.R 105).length+4+4*(S.R 106).length+4 ∧
      Exec body (packedProtectedCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
          110 tailX) 111 tailA) 102 [])}) := by
  let S' : Stacks 117 A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
    110 tailX) 111 tailA) 102 [])}
  have hoff (r : CR) : cr r ≠ (105 : Fin 117) ∧ cr r ≠ 106 := by
    have hr := (cr_range r).2.1
    constructor <;> intro he <;> have hv := congrArg Fin.val he <;> omega
  have hcall (v₀ : HS 117 Q A U) (_ : v₀.user = v.user) :
      ∃ v₁ m, v₁.user = v₀.user ∧
        m ≤ generatedReadyRowCost L q w (S.R 100).length+
          4*((S.R 97).length+(S.R 98).length+(S.R 99).length)+12 ∧
        Exec body (protectedCouplingRow hQ) (mk v₀ (parkedHeaders [105,106] S)) m
          (mk v₁ (parkedHeaders [105,106] S')) := by
    obtain ⟨v₁,m,hu,hm,he⟩ := protectedCouplingRow_exec (body := body) hQ hA hw5 hqw xs as rhs
      hxlen halen hxs has v₀ (parkedHeaders [105,106] S) tailX tailA tailR
      (by simpa using hL) (by simpa using hwR) (by simpa using hq)
      (by simpa using hx) (by simpa using ha) (by simpa using hrhs)
      (by intro i
          have hn : mul i ∉ ([(105 : Fin 117),106] : List (Fin 117)) := by
            have hi := i.isLt
            simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,ne_eq,Fin.ext_iff,mul]
            constructor <;> omega
          exact ⟨by rw [parkedHeaders_L_off _ _ _ hn]; exact (hc i).1,
            by simpa only [parkedHeaders_R,if_neg hn] using (hc i).2⟩)
      (by intro r; simpa [hoff r] using hblank r)
      (by intro k hk
          have hn : k ∉ [(105 : Fin 117),106] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl <;> decide
          rw [parkedHeaders_L_off _ _ _ hn]; exact hleft k hk)
      (by intro k hk hn
          by_cases hm : k ∈ [(105 : Fin 117),106]
          · simp [hm]
          · have hz := hwork k hk (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using (show k ∉ [(97 : Fin 117),98,99,105,106] from by simp_all))
            simpa [hm] using hz)
      (by simpa using h109)
    refine ⟨v₁,m,hu,by simpa using hm,he.cast rfl ?_⟩
    apply congrArg (mk v₁)
    refine Stacks.ext (by rfl) (by rfl) ?_ ?_
    · simp [S',parkedHeaders,parkedHeader]
    · funext r
      by_cases h1 : r = 105 <;> by_cases h2 : r = 106 <;>
        by_cases h3 : r = 113 <;> by_cases h4 : r = 110 <;>
        by_cases h5 : r = 111 <;> by_cases h6 : r = 102 <;>
        simp [S',parkedHeaders,parkedHeader,h1,h2,h3,h4,h5,h6]
  obtain ⟨v',m,hu,hm,he⟩ := withSavedHeaders_exec (body := body) [105,106] (by decide)
    (protectedCouplingRow hQ) v S S' _ hmetaLeft (by simpa [S'] using hmetaLeft)
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> simp [S']) hcall
  exact ⟨v',m,hu,by simpa [List.map_cons,List.map_nil,Nat.add_assoc] using hm,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
