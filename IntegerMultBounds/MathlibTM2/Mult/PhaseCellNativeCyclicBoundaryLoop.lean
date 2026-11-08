module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeCyclicBoundaryRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Structural replica traversal for native boundary recovery. One shared
factor page and two retained masks serve every row of an arbitrary list. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def nativeCyclicBoundaryLoopState (S : Stacks 240 A)
    (source output count : List (Fin (A+4))) : Stacks 240 A :=
  {S with R := (Function.update (Function.update (Function.update S.R 224 source) 132 output) 228 count)}

theorem nativeCyclicBoundaryLoop_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (q w W : ℕ) (rows : List (List GaussianInt))
    (hlens : ∀ row ∈ rows, row.length = (cyclicPrincipalBoundary s t band a n).card)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail : List (Fin (A+4)))
    (hwork : NativeBoundaryUnfoldWorkspace (cyclicPrincipalBoundary s t band a n).card
      (embStk (Fin.castLE (by decide : 234 ≤ 240)) S))
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk (Fin.castLE (by decide : 224 ≤ 240)) S)) q w W
      (cyclicPrincipalBoundary s t band a n).card)
    (hleft : ∀ i, S.L i = [])
    (hsource : S.R 224 = rows.flatMap (cstream A w)++tail)
    (hmaskR : S.R 238 = couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hmaskL : S.R 239 = couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)))
    (hfresh : ∀ i ∈ ([(231 : Fin 240),232,233,234,235,236,237]), S.R i = [])
    (hcount : (S.R 228).length = rows.length) :
    let B := cyclicPrincipalBoundary s t band a n
    let fields := fun solution =>
      cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
        cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
    ∃ vf m, vf.user = v.user ∧ m ≤ rows.length*(nativeCyclicBoundaryRowCost B.card n w+3)+2 ∧
      Exec body (countedLoop 228 nativeCyclicBoundaryRow) (mk v S) m
        (mk vf (nativeCyclicBoundaryLoopState S tail (rows.reverse.flatMap fields++S.R 132) [])) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t band a n
  let fields := fun solution =>
    cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
      cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
  let Inv := fun j (F : Stacks 240 A) => ∃ done todo count,
    rows = done++todo ∧ done.length = j ∧
    F = nativeCyclicBoundaryLoopState S (todo.flatMap (cstream A w)++tail)
      (done.reverse.flatMap fields++S.R 132) count ∧
    NativeBoundaryUnfoldWorkspace B.card (embStk (Fin.castLE (by decide : 234 ≤ 240)) F) ∧
    BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240)) F)) q w W B.card
  have hstable : ∀ j F xs, Inv j F → Inv j {F with R := Function.update F.R 228 xs} := by
    intro j F xs hI
    obtain ⟨done,todo,count,heq,hlen,hstate,hwF,hrF⟩ := hI
    refine ⟨done,todo,xs,heq,hlen,?_,?_,?_⟩
    · rw [hstate]; simp only [nativeCyclicBoundaryLoopState,Function.update_idem]
    · have h228 : (228 : Fin 240) = Fin.castLE (by decide : 234 ≤ 240) (228 : Fin 234) := rfl
      rw [h228,embStk_updateR (Fin.castLE_injective _)]
      exact hwF.updateR 228 xs (by decide) (by decide) (by decide) (by decide)
    · have hfactor : boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240))
          {F with R := Function.update F.R 228 xs}) =
          boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240)) F) := by
        funext r
        apply Function.update_of_ne
        intro he
        have hv := congrArg (fun k : Fin 240 => k.val) he
        have hr := (boundaryFactorReg r).isLt
        change (boundaryFactorReg r).val = 228 at hv
        omega
      rw [hfactor]; exact hrF
  have hstep : ∀ j < rows.length, ∀ (vi : HS 240 Q A U) F, Inv j F →
      ∃ vf G m, vf.user = vi.user ∧ m ≤ nativeCyclicBoundaryRowCost B.card n w ∧
        Exec body nativeCyclicBoundaryRow (mk vi F) m (mk vf G) ∧ G.R 228 = F.R 228 ∧ Inv (j+1) G := by
    intro j hj vi F hI
    obtain ⟨done,todo,count,heq,hlen,hstate,hwF,hrF⟩ := hI
    cases todo with
    | nil => simp only [List.append_nil] at heq; have hh := congrArg List.length heq; omega
    | cons row todo =>
      have hrow : row ∈ rows := by rw [heq]; simp
      have hsrc : F.R 224 = cstream A w row++(todo.flatMap (cstream A w)++tail) := by
        rw [hstate]; simp [nativeCyclicBoundaryLoopState,List.flatMap_cons,List.append_assoc]
      obtain ⟨vf,m,hu,hm,he,hwG,hrG⟩ := nativeCyclicBoundaryRow_exec (body := body)
        hst hA band a n ha hn q w W row (hlens row hrow) vi F
        (todo.flatMap (cstream A w)++tail) hwF hrF
        (by intro i; rw [hstate]; exact hleft i) hsrc
        (by rw [hstate]; simpa [nativeCyclicBoundaryLoopState] using hmaskR)
        (by rw [hstate]; simpa [nativeCyclicBoundaryLoopState] using hmaskL)
        (by intro i hi
            rw [hstate]
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals simpa [nativeCyclicBoundaryLoopState] using hfresh _ (by simp))
      refine ⟨vf,_,m,hu,hm,he,?_,done++[row],todo,count,?_,?_,?_,hwG,hrG⟩
      · simp [nativeCyclicBoundaryRowState,nativeCyclicBoundaryRecoveryState]
      · simpa only [List.append_assoc,List.singleton_append] using heq
      · simp [hlen]
      · rw [hstate]
        refine Stacks.ext rfl rfl rfl ?_
        funext k
        by_cases hk132 : k = 132 <;> by_cases hk224 : k = 224 <;> by_cases hk228 : k = 228 <;>
          simp [nativeCyclicBoundaryRowState,nativeCyclicBoundaryRecoveryState,nativeCyclicBoundaryLoopState,
            hk132,hk224,hk228,List.reverse_append,fields,B,List.append_assoc]
  have hinit : Inv 0 S := by
    refine ⟨[],rows,S.R 228,rfl,rfl,?_,hwork,hready⟩
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk132 : k = 132 <;> by_cases hk224 : k = 224 <;> by_cases hk228 : k = 228 <;>
      simp [nativeCyclicBoundaryLoopState,hk132,hk224,hk228,hsource]
  obtain ⟨vf,F,m,hu,hm,he,h228,hI⟩ := countedLoop_exec (body := body)
    228 nativeCyclicBoundaryRow rows.length (nativeCyclicBoundaryRowCost B.card n w) Inv
    hstable hstep v S hcount hinit
  obtain ⟨done,todo,count,heq,hlen,hstate,_,_⟩ := hI
  have ht : todo = [] := by
    have hh := congrArg List.length heq
    simp only [List.length_append] at hh
    apply List.eq_nil_of_length_eq_zero
    omega
  subst todo
  simp only [List.append_nil] at heq
  subst done
  have hc : count = [] := by simpa [hstate,nativeCyclicBoundaryLoopState] using h228
  subst count
  exact ⟨vf,m,hu,hm,he.cast rfl (congrArg (mk vf) hstate)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
