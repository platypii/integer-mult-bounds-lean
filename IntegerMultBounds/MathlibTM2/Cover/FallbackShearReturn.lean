module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackReturnWord
public import IntegerMultBounds.MathlibTM2.Cover.FallbackScheduledShear

/-! Normalize the computed shear word with the counters retained by the shear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {P U : Type} {T M d W A : ℕ} [NeZero M]

def returnPorts : Fin 8 ↪ Fin 29 := ⟨![25,24,19,20,21,22,16,3],by decide⟩

def finishShear (r : Fin 29 ↪ Fin T) : Pr P T 217 A U :=
  .seq (Routing.binaryCanonicalCopyProgram (r 13) (r 3) (r 4) (r 5)) (returnWord (returnPorts.trans r))

theorem finishShear_exec (body : P → Pr P T 217 A U) (r : Fin 29 ↪ Fin T) (t : Fin d) (hW : 0 < W)
    (source dest : ℤ → Fin (A+4)) (p q : ℤ) (a word : Fin (M^d*W) → Fin (A+4))
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (L : ℕ) (v : HS T 217 A U) (S : Stacks T A)
    (ready : PrefixCopyReady (r 13) (r 3) (r 4) (r 5) L (prefixSize (Q := M) t) S)
    (counters : ShearCounters (suffixSize (Q := M) (W := W) t) M (r ∘ shearTranslation) S)
    (dst : ∀ z, readAt blank (S.L (r 25)) (S.R (r 25)) (z-(q+(M^d*W : ℕ))) = putWord dest q (List.ofFn word) z)
    (src : ∀ z, readAt blank (S.L (r 24)) (S.R (r 24)) (z-(p+(M^d*W : ℕ))) = putWord source p (List.ofFn a) z) :
    ∃ u F n, u.user = v.user ∧ n ≤ 10*L+12+((327*(M^d*W)+2)*13+6) ∧
      Exec body (finishShear r) (mk v S) n (mk u F) ∧
      (∀ z, readAt blank (F.L (r 24)) (F.R (r 24)) (z-p) = putWord source p (List.ofFn word) z) ∧
      (∀ z, readAt blank (F.L (r 25)) (F.R (r 25)) (z-q) = dest z) ∧
      ∀ j, (∀ i, r (returnPorts i) ≠ j) → F.R j = S.R j := by
  obtain ⟨bs,qs,hb,hq,cb,cq,clock,inner⟩ := counters
  obtain ⟨ps,y,cp,hp,hy,install,descriptor⟩ := installPrefixCount_exec body r v S ready
  let D : Stacks T A := {S with R := Function.update S.R (r 3) (ps.map bitSymbol)}
  have keep (i : Fin 29) (ne : i ≠ 3) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne ne) _ _
  obtain ⟨u,F,n,hu,hn,run,rep,frame⟩ := returnWord_exec body (returnPorts.trans r) t hW source dest p q a word
    bs qs ps hb hq hp cb cq cp empty y D
    (by change ∀ z, readAt blank _ (D.R (r 25)) _ = _; rwa [keep 25 (by decide)])
    (by change ∀ z, readAt blank _ (D.R (r 24)) _ = _; rwa [keep 24 (by decide)])
    (by
      intro i z
      fin_cases i
      all_goals first | exact descriptor z | (
        change _ = readAt blank _ (D.R (r _)) _
        rw [keep _ (by decide)]
        first | exact inner 0 z | exact inner 1 z | exact inner 2 z | exact inner 3 z | exact clock z))
  exact ⟨u,F,_,hu.trans hy,Nat.add_le_add_left hn _,Exec.seq install run,
    fun z => (rep 1 z).symm,fun z => (rep 0 z).symm,fun j hj =>
      (frame j hj).2.trans (Function.update_of_ne (hj 7).symm _ _)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
