module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInit
public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugationRun

/-! Initialize the shared formula pool and run packed matrix conjugation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι P U : Type} {T Q A m D : ℕ}

theorem initializedConjugation_exec (body : P → Pr P T Q A U)
    (p w : ℕ) (hp : p.Prime) [NeZero (p^(w+1))]
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod (p^(w+1)))) (b proj : ι) (unit : IsUnit (mat b).det)
    (r : Fin 16 ↪ Fin T) (clock count : Fin T) (copyPorts : [clock,count,r 2,r 3].Nodup)
    (outside : ∀ i, r i ≠ count) (clockPivot : clock ≠ r 14)
    (H : ℕ) (hm : p^(w+1) < 2^H)
    (pool : Fin ((D+1)*13) ↪ Fin T) (source : Leaf (Entry ι m) → Fin 7 ↪ Fin T)
    (apart : ∀ a i j, source a i ≠ pool j) (q : Fin 14 ↪ Fin T)
    (rPool : ∀ i k, r i ≠ pool k) (srcPivot : ∀ a i, source a i ≠ r 14)
    (clockPool : ∀ k, clock ≠ pool k) (countPool : ∀ k, count ≠ pool k) (srcInv : ∀ a i, source a i ≠ r 0)
    (qPivot : ∀ j, q j ≠ r 14) (shared : q 0 = r 0)
    (qPool : ∀ i k, q i ≠ pool k)
    (srcFree : ∀ a i j, j = 1 ∨ j = 13 → source a i ≠ q j) :
    let num := fun i j : Fin m => numerator (matrixInput b) (matrixInput proj) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
    (∀ i j, (num i j).depth ≤ D) →
    let f := determinant (matrixInput b)
    f.depth ≤ D →
    let C := 48*H*H+152*H+66
    ∀ (v : HS T Q A U) (S : Stacks T A),
    let R := S.R
    (R clock).length = w → R count = [] → R (r 14) = [] →
      R (r 15) = binSyms H (1 : ZMod (p^(w+1))).val → R (r 4) = binSyms H (p^(w+1)) →
      (∀ i : Fin 16, i ≠ 4 → i < 13 → R (r i) = []) →
      (∀ j, R (pool j) = []) →
      (∀ a, leafReady (fun c _ => source c) mat H a (source a 3) R) →
      R (q 2) = binSyms H (p^(w+1)) → R (q 13) = [] →
      (∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (q k) = []) →
      ∃ z F t, z.user = v.user ∧ Exec body (.seq (initFrames pool (r 4) (D+1))
      (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (r 14)) (reusablePivotInverse p r clock count))
        (.seq (packedConjugate pool source q b proj) (.seq (bclear (r 0)) (bclear (r 14)))))
      ) (mk v S) t (mk z F) ∧
      F.R (q 3) = matrixWords A H (mat b * mat proj * (mat b)⁻¹) ++ R (q 3) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ k ≤ D, F.R (frame pool k 2) = binSyms H (p^(w+1))) ∧
      (∀ i, i ≠ q 3 → (∀ k ≤ D, i ≠ frame pool k 2) → F.R i = R i) ∧
      t ≤ (D+1)*(6*H+6)+1 +
      (time H (readTime H) f + (6*w+6+(14*H+16+(p-2)*C+C+w*(12*H+15+p*C))) +
       ((m*(m*(cost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) := by
  intro num cost fits f detFits C v S R ticks countBlank pivot oneWord modulus free blank inputs modQ blankQ freeQ
  obtain ⟨u,B,hu,init,inp,out,left,filled,keep⟩ := initFrames_exec body pool (r 4) (rPool 4) v S blank (D+1) le_rfl
  have same (i) (h : ∀ j, i ≠ pool j) := keep i (fun _ _ => h _)
  have srcEq (a i) := same (source a i) (apart a i)
  have leaves (a) : leafReady (fun c _ => source c) mat H a (source a 3) B.R := by
    have h := inputs a
    cases a <;> simpa only [leafReady,srcEq] using h
  have scratch (k) (hk : k ≤ D) (i : Fin 13) (hi : i ≠ 2) : B.R (frame pool k i) = [] := by
    apply Eq.trans (keep _ _) (blank _)
    intro l hl
    rcases lt_trichotomy l k with h | h | h
    · exact separate pool h hk i 2
    · subst l; exact (frame pool k).injective.ne hi
    · exact (separate pool h (by omega) 2 i).symm
  obtain ⟨z,n,hz,hn,run⟩ := conjugationRun_writes body p w hp mat b proj unit r clock count copyPorts outside clockPivot
    H hm pool source apart q (fun k => (rPool 14 k).symm) srcPivot (fun k => (rPool 0 k).symm) srcInv
    qPivot shared (fun k j _ => (qPool j k).symm) srcFree fits detFits u B
    ⟨(congrArg List.length (same clock clockPool)).trans ticks,(same count countPool).trans countBlank,
      (same _ (rPool 14)).trans pivot,(same _ (rPool 15)).trans oneWord,(same _ (rPool 4)).trans modulus,
      fun i hi hj => (same _ (rPool i)).trans (free i hi hj),fun k hk => (filled k (by omega)).trans modulus,
      scratch,leaves,(same _ (qPool 2)).trans modQ,(same _ (qPool 13)).trans blankQ,
      fun k hk => (same _ (qPool k)).trans (freeQ k hk)⟩
  refine ⟨z,_,_,hz.trans hu,Exec.seq init run,?_,inp,out,left,?_,?_,?_⟩
  · simp [same _ (qPool 3),R]
  · intro k hk
    exact (Function.update_of_ne (qPool 3 _).symm _ _).trans ((filled k (by omega)).trans modulus)
  · intro i hi h
    exact (Function.update_of_ne hi _ _).trans (keep i (fun k hk => h k (by omega)))
  · change S.R (r 4) = _ at modulus
    rw [modulus,length_binSyms]
    exact Nat.add_le_add_left hn _

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
