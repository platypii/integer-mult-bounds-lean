module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInputs
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotInverse

/-! Compile the determinant of a packed matrix and invert it on the reusable clock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι P U : Type} {T Q A m : ℕ}

theorem denominatorInverse_exec (body : P → Pr P T Q A U)
    (ports : Leaf (Entry ι m) → Fin T → Fin 7 ↪ Fin T) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (p w : ℕ) (hp : p.Prime) [NeZero (p^(w+1))]
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod (p^(w+1)))) (b : ι) (unit : IsUnit (mat b).det)
    (r : Fin 16 ↪ Fin T) (clock count : Fin T) (copyPorts : [clock,count,r 2,r 3].Nodup)
    (outside : ∀ i, r i ≠ count) (clockPivot : clock ≠ r 14)
    (H : ℕ) (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A)
    (ticks : (S.R clock).length = w) (empty : S.R count = []) (pivot : S.R (r 14) = [])
    (one : S.R (r 15) = binSyms H (1 : ZMod (p^(w+1))).val)
    (modulus : S.R (r 4) = binSyms H (p^(w+1)))
    (free : ∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (r i) = []) :
    let f := determinant (matrixInput b)
    let C := 48*H*H+152*H+66
    prepared bank (entryValue mat) H (leafReady ports mat H) f 0 (r 14) S.R →
    ∃ z F t, z.user = v.user ∧ t ≤ time H (readTime H) f +
      (6*w+6+(14*H+16+(p-2)*C+C+w*(12*H+15+p*C))) ∧
      Exec body (.seq (compile (readLeaf ports) bank f 0 (r 14)) (reusablePivotInverse p r clock count))
        (mk v S) t (mk z F) ∧
      F.R (r 0) = binSyms H (Ring.inverse (mat b).det).val ∧ F.R (r 14) = binSyms H (mat b).det.val ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧ ∀ i, i ≠ r 0 → i ≠ r 14 → F.R i = S.R i := by
  intro f C ready
  obtain ⟨u,n,hu,hn,det⟩ := determinant_writes body ports bank mat H hm b (r 14) v S ready
  rw [pivot,List.append_nil] at det
  let B := {S with R := Function.update S.R (r 14) (binSyms H (mat b).det.val)}
  have keep (i) (hi : i ≠ r 14) : B.R i = S.R i := Function.update_of_ne hi _ _
  obtain ⟨z,F,t,hz,ht,inv,_,result,left,inp,out,frame⟩ :=
    reusablePivotInverse_exec body p w hp _ unit r clock count copyPorts outside H hm u B
      (by rwa [keep _ clockPivot]) ((keep _ (outside 14).symm).trans empty) (Function.update_self ..)
      ((keep _ (r.injective.ne (by decide))).trans one) ((keep _ (r.injective.ne (by decide))).trans modulus)
      (fun i hi hj => (keep _ (r.injective.ne (by omega))).trans (free i hi hj))
  exact ⟨z,F,_,hz.trans hu,Nat.add_le_add hn ht,Exec.seq det inv,result,
    (frame _ (r.injective.ne (by decide))).trans (Function.update_self ..),left,inp,out,
    fun i hi hj => (frame i hi).trans (keep i hj)⟩

/-- Use the reciprocal for a restoring writer, then release both determinant registers. -/
theorem withDenominator_writes (body : P → Pr P T Q A U)
    (ports : Leaf (Entry ι m) → Fin T → Fin 7 ↪ Fin T) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (p w : ℕ) (hp : p.Prime) [NeZero (p^(w+1))]
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod (p^(w+1)))) (b : ι) (unit : IsUnit (mat b).det)
    (r : Fin 16 ↪ Fin T) (clock count : Fin T) (copyPorts : [clock,count,r 2,r 3].Nodup)
    (outside : ∀ i, r i ≠ count) (clockPivot : clock ≠ r 14)
    (H : ℕ) (hm : p^(w+1) < 2^H)
    (dst : Fin T) (hd : dst ≠ r 0) (hpiv : dst ≠ r 14)
    (ok : Regs T A → Prop) (prog : Pr P T Q A U) (word : List (Fin (A+4))) (cost : ℕ)
    (write : Writes body ok dst prog word cost) :
    let f := determinant (matrixInput b)
    let C := 48*H*H+152*H+66
    Writes body (fun R => (R clock).length = w ∧ R count = [] ∧ R (r 14) = [] ∧
      R (r 15) = binSyms H (1 : ZMod (p^(w+1))).val ∧ R (r 4) = binSyms H (p^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → R (r i) = []) ∧
      prepared bank (entryValue mat) H (leafReady ports mat H) f 0 (r 14) R ∧
      ok (Function.update (Function.update R (r 14) (binSyms H (mat b).det.val)) (r 0)
        (binSyms H (Ring.inverse (mat b).det).val))) dst
      (.seq (.seq (compile (readLeaf ports) bank f 0 (r 14)) (reusablePivotInverse p r clock count))
        (.seq prog (.seq (bclear (r 0)) (bclear (r 14))))) word
      (time H (readTime H) f + (6*w+6+(14*H+16+(p-2)*C+C+w*(12*H+15+p*C))) + cost + 4*H+4) := by
  intro f C v S ⟨ticks,empty,pivot,oneWord,modulus,free,ready,okStore⟩
  obtain ⟨u,B,n,hu,hn,compute,inv,det,left,inp,out,keep⟩ := denominatorInverse_exec body ports bank
    p w hp mat b unit r clock count copyPorts outside clockPivot H hm v S ticks empty pivot oneWord modulus free ready
  have diff := r.injective.ne (by decide : (14 : Fin 16) ≠ 0)
  have regs : B.R = _ := show B.R = Function.update (Function.update S.R (r 14)
      (binSyms H (mat b).det.val)) (r 0) (binSyms H (Ring.inverse (mat b).det).val) by
    funext i
    by_cases hi : i = r 0
    · subst i; simpa using inv
    by_cases hj : i = r 14
    · subst i; simpa [Function.update_of_ne diff] using det
    simpa [Function.update_of_ne hi,Function.update_of_ne hj] using keep i hi hj
  obtain ⟨y,t,hy,ht,run⟩ := write u B (regs ▸ okStore)
  let E := {B with R := Function.update B.R dst (word ++ B.R dst)}
  obtain ⟨z,hz,_,clearInv⟩ := bclear_exec body (r 0) y E
  let F := {E with R := Function.update E.R (r 0) []}
  obtain ⟨a,ha,_,clearDet⟩ := bclear_exec body (r 14) z F
  have l₀ : (E.R (r 0)).length = H := by simp [E,Function.update_of_ne hd.symm,inv,length_binSyms]
  have l₁ : (F.R (r 14)).length = H := by simp [F,E,Function.update_of_ne hpiv.symm,det,length_binSyms]
  have final : {F with R := Function.update F.R (r 14) []} = {S with R := Function.update S.R dst (word ++ S.R dst)} := by
    congr 1
    · funext i
      by_cases h : i = r 14
      · subst i; simp [Function.update_of_ne hpiv.symm,pivot]
      by_cases k : i = r 0
      · subst i; simp [F,Function.update_of_ne hd.symm,free 0 (by decide) (by decide)]
      simp only [F,E,Function.update_of_ne h,Function.update_of_ne k,keep dst hd hpiv]
      by_cases d : i = dst
      · subst i; simp
      simpa [Function.update_of_ne d] using keep i k h
  rw [final] at clearDet
  refine ⟨a,_,ha.trans (hz.trans (hy.trans hu)),?_,Exec.seq compute (Exec.seq run (Exec.seq clearInv clearDet))⟩
  dsimp only [f,C]; rw [l₀,l₁]; omega

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
