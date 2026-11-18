module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberBank
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalCopy

/-! A modular shear with width, modulus and coefficient supplied in arithmetic registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Routing
variable {T A : ℕ} {P U : Type}

def dimensionShear (r : Fin 13 ↪ Fin T) (call : Fin 12 ↪ Fin T) (count : Fin T) : Pr P T 217 A U :=
  .seq (binaryCanonicalCopyProgram (r 12) (call 5) (r 4) (r 5))
    (.seq (binaryCanonicalCopyProgram (r 2) (call 7) (r 4) (r 5))
      (.seq (initializeBank call) (shearProgram r call count)))

theorem dimensionShear_exec (body : P → Pr P T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L K c M B : ℕ) (hwidth : B < 2^K) (hc : c < M) (hM : M < 2^L) (hB : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A) (coef : S.R (r 0) = binSyms L c)
    (modulus : S.R (r 2) = binSyms L M) (width : S.R (r 12) = binSyms K B) (digit : S.R (r 1) = [])
    (scratch : ∀ i : Fin 13, 3 ≤ i → i < 12 → S.R (r i) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B)
    (empty : S.R count = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (call i) = [])
    (right : ∀ i : Fin 12, i < 10 → S.R (call i) = [])
    (src : ∀ k, RadixToBinary.binaryEncoding.encode
      (putWord source p (TranslationStream.fibers M M payload).flatten k) =
        readAt blank (S.L (call 10)) (S.R (call 10)) (k-p))
    (dst : ∀ k, RadixToBinary.binaryEncoding.encode (dest k) =
        readAt blank (S.L (call 11)) (S.R (call 11)) (k-q)) :
    ∃ bs ms z F n, Counter.value bs = B ∧ Counter.value ms = M ∧ z.user = v.user ∧ n ≤ 6*M+25*L+10*K+35 + M*(48*L*L+162*L+93+(207*(M*B)+241)*25)+2 ∧
      Exec body (dimensionShear r call count) (mk v S) n (mk z F) ∧
      F.R count = [] ∧ FiberReady r L c M M F ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (shearBank M B c source dest p q payload bs ms M)) (F.L ∘ call) (F.R ∘ call) := by
  have dis (i : Fin 13) (j : Fin 12) (hj : j ≠ 8) : r i ≠ call j := by
    by_cases h : i = 3
    · subst i; rw [← slot]; exact call.injective.ne hj.symm
    · exact (outside i h j).symm
  have d5 (i : Fin 13) := dis i 5 (by decide)
  have d7 (i : Fin 13) := dis i 7 (by decide)
  have s4 := scratch 4 (by decide) (by decide)
  have s5 := scratch 5 (by decide) (by decide)
  obtain ⟨bs,u,cb,hb,_,hu,wb⟩ := binaryCanonicalCopy_exec body (r 12) (call 5) (r 4) (r 5)
    (by simp [List.nodup_cons,r.injective.eq_iff,d5,Ne.symm (d5 4),Ne.symm (d5 5)])
    K B hwidth v S width (right 5 (by decide)) s4 s5
  let D : Stacks T A := {S with R := Function.update S.R (call 5) (bs.map bitSymbol)}
  obtain ⟨ms,u',cm,hm,_,hu',wm⟩ := binaryCanonicalCopy_exec body (r 2) (call 7) (r 4) (r 5)
    (by simp [List.nodup_cons,r.injective.eq_iff,d7,Ne.symm (d7 4),Ne.symm (d7 5)])
    L M hM u D (by simpa [D,Function.update_of_ne (d5 2)] using modulus)
    (by simpa [D,call.injective.eq_iff] using right 7 (by decide))
    (by simpa [D,Function.update_of_ne (d5 4)] using s4)
    (by simpa [D,Function.update_of_ne (d5 5)] using s5)
  let E : Stacks T A := {D with R := Function.update D.R (call 7) (ms.map bitSymbol)}
  have keep (i : Fin 13) : E.R (r i) = S.R (r i) := by
    simp [E,D,Function.update_of_ne (d5 i),Function.update_of_ne (d7 i)]
  obtain ⟨z,F,n,hz,hn,run,rest,ready,final⟩ := initializedShear_exec body r call slot outside
    count hr ht L c M B hc hM hB u' E ((keep 0).trans coef) ((keep 2).trans modulus)
    ((keep 1).trans digit) (fun i hi hj => (keep i).trans (scratch i hi hj)) source dest p q payload hw
    bs ms hb hm cb cm (by simpa [E,D,Function.update_of_ne (ht 5).symm,Function.update_of_ne (ht 7).symm] using empty)
    left (by
      intro i hi
      by_cases h : i = 5
      · subst i; simp [E,D,call.injective.eq_iff]
      · by_cases h' : i = 7 <;> simp [E,D,call.injective.eq_iff,h,h',right i hi])
    (by simpa [E,D,call.injective.eq_iff] using src)
    (by simpa [E,D,call.injective.eq_iff] using dst)
  exact ⟨bs,ms,z,F,_,hb,hm,hz.trans (hu'.trans hu),by omega,
    Exec.seq wb (Exec.seq wm run),rest,ready,final⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
