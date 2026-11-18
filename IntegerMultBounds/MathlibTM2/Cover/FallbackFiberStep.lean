module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberRun
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! A recurring fiber step for a tape-supplied modular shear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host TranslationExecutionReuse
variable {T A : ℕ} {P U : Type}

structure FiberReady (r : Fin 13 ↪ Fin T) (L c x M : ℕ) (S : Stacks T A) : Prop where
  coef : S.R (r 0) = binSyms L c
  digit : S.R (r 1) = binSyms L x
  modulus : S.R (r 2) = binSyms L M
  empty : ∀ i : Fin 13, 3 ≤ i → i < 12 → S.R (r i) = []
  marker : S.L (r 3) = [separator]

def fiberStep (r : Fin 13 ↪ Fin T) (call : Fin 12 ↪ Fin T) : Pr P T 217 A U :=
  .seq (fiberProgram r call) (countIter (r 1) (r 4) (r 12))

theorem fiberStep_exec (body : P → Pr P T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (L c x M B : ℕ) (hc : c < M) (hx : x < M) (hM : M < 2^L) (hB : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A) (ready : FiberReady r L c x M S)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4))) (bs ms : List Bool)
    (hlen : blocks.length = M) (hw : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (input source dest p q blocks bs ms [])) (S.L ∘ call) (S.R ∘ call)) :
    ∃ z F n, Exec body (fiberStep r call) (mk v S) n (mk z F) ∧
      n ≤ 48*L*L+162*L+90+(207*(M*B)+241)*25 ∧ FiberReady r L c (x+1) M F ∧
      z.user = v.user ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ j, call j ≠ k) → k ≠ r 1 → F.L k = S.L k ∧ F.R k = S.R k) ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (output M (c*x % M) B source dest p q blocks bs ms [])) (F.L ∘ call) (F.R ∘ call) := by
  obtain ⟨u,D,n,mark,empty,run,time,hu,hin,hout,frame,translated⟩ :=
    fiberProgram_exec body r call slot L c x M hc hx hM v S ready.coef ready.digit ready.modulus
      ready.empty ready.marker source dest p q blocks bs ms rep B hB hlen hw hb hm cb cm
  have kept (i : Fin 13) (hi : i ≠ 3) := (frame (r i) (outside i hi)).2
  obtain ⟨z,hz,advance⟩ := countIter_exec body (r.injective.ne (by decide : (1 : Fin 13) ≠ 4))
    (r 12) u D ((kept 1 (by decide)).trans ready.digit)
    ((kept 4 (by decide)).trans (ready.empty 4 (by decide) (by decide)))
  refine ⟨z,_,_,Exec.seq run advance,by omega,?_,hz.trans hu,hin,hout,?_,?_⟩
  · constructor
    · simpa [r.injective.eq_iff] using (kept 0 (by decide)).trans ready.coef
    · simp
    · simpa [r.injective.eq_iff] using (kept 2 (by decide)).trans ready.modulus
    · intro i hi hj
      have hne : r i ≠ r 1 := r.injective.ne (by omega)
      simp only [Function.update_of_ne hne]
      by_cases h : i = 3
      · simpa [h,slot] using empty
      · exact (kept i h).trans (ready.empty i hi hj)
    · simpa [slot] using mark
  · intro k hk hd
    simpa [Function.update_of_ne hd] using frame k hk
  · intro i j
    simpa [Function.comp_apply,Function.update_of_ne (outside 1 (by decide) i)] using translated i j

end IntegerMultBounds.MathlibTM2.Cover.Fallback
