module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchFromOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedGroupWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedClosedHaloGroup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOriginPackets

/-! Execute a nonempty equal-length halo group with retained weights and the closed batch
solver and the original ambient matrix. Raw RHS gathering remains separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

noncomputable def cachedProtectedHaloBatchSolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  .seq (ucopy 116 129 133)
    (embProg cachedGroupReg Empty.elim (cachedBatchFromOrigins (P₀ := Empty) hR hQ))

theorem cachedProtectedHaloBatchSolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hgroup : 0 < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 148 Q A U) (S₀ : Stacks 148 A) (tail borrowed cacheTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    let lo := haloGroupOrigin s t (PhaseCellBand.width p u) a b L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
    (embStk weightCacheCoreReg (embStk cachedGroupReg S₀) = batchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B
      (fun n => (lo n).val) rhs borrowed tail inp out) →
    S₀.R 144 = batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val)++cacheTail →
    (S₀.R 145).length = 2*(B*(L*w)) → S₀.R 146 = [] → S₀.R 147 = [] → S₀.R 129 = [] → S₀.R 133 = [] →
    ∃ v' S' m, v'.user = v.user ∧ m ≤ (4*B+4)+cachedBatchFromOriginsCost p l B L s t u target rhsExp ∧
      Exec body (cachedProtectedHaloBatchSolve hR hQ)
        (mk v S₀) m (mk v' S') ∧
      S'.R 129 = List.replicate B tick ∧ S'.L = S₀.L ∧
      (∀ i, 117 ≤ i.val → i ≠ 129 → S'.L i = S₀.L i ∧ S'.R i = S₀.R i) ∧
      (embStk weightCacheCoreReg (embStk cachedGroupReg S')).inp = inp ∧ (embStk weightCacheCoreReg (embStk cachedGroupReg S')).out = out ∧ (∀ k, (embStk weightCacheCoreReg (embStk cachedGroupReg S')).L k = []) ∧ (embStk weightCacheCoreReg (embStk cachedGroupReg S')).R 110 = rhs ++ borrowed ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk weightCacheCoreReg (embStk cachedGroupReg S')).R k = []) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord ((((embStk weightCacheCoreReg (embStk cachedGroupReg S')).R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) ((embStk weightCacheCoreReg (embStk cachedGroupReg S')).R 93)) x (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp), ys.val.length = B*L*w ∧ (embStk weightCacheCoreReg (embStk cachedGroupReg S')).R 93 = ys ++ tail := by
  dsimp only
  intro hinput hcache hcacheCount h146 h147 h129 h133
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  have h116 : (S₀.R 116).length = B := by
    have hh := congrArg (fun E : Stacks 117 A => (E.R 116).length) hinput
    simpa [embStk,weightCacheCoreReg,cachedGroupReg,batchInputBank,B,band] using hh
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 116) (b := 129) (t := 133)
    (by decide) (by decide) (by decide) v S₀ h133
  let T : Stacks 148 A := {S₀ with R := Function.update S₀.R 129 (List.replicate B tick)}
  have he₁' : Exec body (ucopy 116 129 133) (mk v S₀) (4*B+4) (mk v₁ T) := by
    simpa [T,h116,h129] using he₁
  have hview : embStk cachedGroupReg T = embStk cachedGroupReg S₀ :=
    cachedGroupProject_updateR S₀ 129 (List.replicate B tick) (by decide) (by decide)
  obtain ⟨vi,E,m,hu,hm,he,hoff,hrest⟩ := cachedClosedHaloGroup_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget hgroup hpad C hC x hx
    (embDn cachedGroupReg v₁) (embStk cachedGroupReg T) tail borrowed cacheTail inp out
    (by rw [hview]; exact hinput)
    (by simpa [T,embStk,cachedGroupReg] using hcache)
    (by simpa [T,embStk,cachedGroupReg] using hcacheCount)
    (by simpa [T,embStk,cachedGroupReg] using h146)
    (by simpa [T,embStk,cachedGroupReg] using h147)
  obtain ⟨v₂,F,he₂,hv₂,hu₂,hproj,hoff₂⟩ := exec_emb (body' := body) (ι := Empty.elim)
    cachedGroupReg_injective (fun p => nomatch p) he v₁ rfl T rfl
  refine ⟨v₂,F,(4*B+4)+m,hu₂.trans (hu.trans hu₁),by dsimp [B,band] at hm ⊢; omega,
    Exec.seq he₁' he₂,?_,?_,?_,?_⟩
  · have h := (hoff₂ 129 (cachedGroupReg_off 129 (by decide) (by decide))).2
    simpa [T] using h
  · funext i
    by_cases hlo : i.val < 117
    · let j : Fin 117 := ⟨i.val,hlo⟩
      have heq : cachedGroupReg (weightCacheCoreReg j) = i := by
        apply Fin.ext
        simp [cachedGroupReg,weightCacheCoreReg,j,hlo]
      have hf := congrArg (fun S : Stacks 121 A => S.L (weightCacheCoreReg j)) hproj
      have hz := hrest.2.2.1 j
      have hi := congrArg (fun S : Stacks 117 A => S.L j) hinput
      have hi' : S₀.L i = [] := by
        simpa only [embStk_L,heq,batchInputBank] using hi
      rw [← heq]
      exact (hf.trans hz).trans (by simpa only [heq] using hi'.symm)
    by_cases hmid : i.val < 144
    · exact (hoff₂ i (cachedGroupReg_off i (by omega) hmid)).1
    · obtain ⟨j,hj,heq⟩ := cachedGroupReg_high i (by omega)
      have h := (congrArg (fun S : Stacks 121 A => S.L j) hproj).trans (hoff j hj).1
      simpa only [embStk_L,heq] using h
  · intro i hi h129i
    by_cases hmid : i.val < 144
    · have h := hoff₂ i (cachedGroupReg_off i hi hmid)
      simpa [T,h129i] using h
    · obtain ⟨j,hj,heq⟩ := cachedGroupReg_high i (by omega)
      have hL := congrArg (fun S : Stacks 121 A => S.L j) hproj
      have hR := congrArg (fun S : Stacks 121 A => S.R j) hproj
      have hL' := hL.trans (hoff j hj).1
      have hR' := hR.trans (hoff j hj).2
      simpa [T,embStk,heq,h129i] using And.intro hL' hR'
  · rw [hproj]
    exact hrest

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
