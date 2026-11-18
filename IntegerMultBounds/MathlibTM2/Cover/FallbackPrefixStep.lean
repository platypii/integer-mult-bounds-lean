module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackControlDigit
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberRun
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Rotate one fiber in the original field order, then advance the physical prefix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host TranslationExecutionReuse
variable {T A : ℕ} {P U : Type}

def digitPorts : Fin 13 ↪ Fin 15 := ⟨![13,14,4,1,5,6,7,8,9,10,12,2,11],by decide⟩
def arithmeticPorts : Fin 13 ↪ Fin 15 := Fin.castLEEmb (by decide)

def prefixStep (r : Fin 15 ↪ Fin T) (call : Fin 12 ↪ Fin T) : Pr P T 217 A U :=
  .seq (controlDigit (digitPorts.trans r)) (.seq (fiberProgram (arithmeticPorts.trans r) call)
    (.seq (bclear (r 1)) (countIter (r 13) (r 4) (r 12))))

theorem prefixStep_exec (body : P → Pr P T 217 A U) (r : Fin 15 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 15, i ≠ 3 → ∀ j, call j ≠ r i)
    (L K H x stride c M B : ℕ) (hx : x < 2^L) (hs : stride < 2^K) (hm : M < 2^H)
    (ps : 0 < stride) (hc : c < M) (hB : 0 < B) (v : HS T 217 A U) (S : Stacks T A)
    (prefixWord : S.R (r 13) = binSyms L x) (gap : S.R (r 14) = binSyms K stride)
    (coef : S.R (r 0) = binSyms H c) (modulus : S.R (r 2) = binSyms H M)
    (blank : ∀ i : Fin 15, 1 ≤ i → i ≤ 12 → i ≠ 2 → S.R (r i) = [])
    (marker : S.L (r 3) = [separator])
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4))) (bs ms : List Bool)
    (hlen : blocks.length = M) (hw : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hv : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (input source dest p q blocks bs ms [])) (S.L ∘ call) (S.R ∘ call)) :
    ∃ z F n, z.user = v.user ∧ n ≤ L*(12*(K+H)+78)+22*K+180*H+170+48*H*H+(207*(M*B)+241)*25 ∧
      Exec body (prefixStep r call) (mk v S) n (mk z F) ∧
      F.R (r 13) = binSyms L (x+1) ∧ F.R (call 8) = [] ∧ F.L (call 8) = [separator] ∧
      (∀ j, (∀ i, call i ≠ j) → j ≠ r 13 → F.R j = S.R j ∧ F.L j = S.L j) ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (output M (c*(x/stride%M)%M) B source dest p q blocks bs ms [])) (F.L ∘ call) (F.R ∘ call) := by
  have pm := Nat.zero_lt_of_lt hc
  have facts : ∀ i : Fin 13, 2 ≤ i → i ≠ 11 →
      1 ≤ digitPorts i ∧ digitPorts i ≤ 12 ∧ digitPorts i ≠ 2 := by decide
  obtain ⟨u,n,hu,hn,get⟩ := controlDigit_exec body (digitPorts.trans r) L K H x stride M
    hx hs hm ps pm v S prefixWord gap modulus (fun i hi hj =>
      blank _ (facts i hi hj).1 (facts i hi hj).2.1 (facts i hi hj).2.2)
  let D : Stacks T A := {S with R := Function.update S.R (r 1) (binSyms H (x/stride%M))}
  have kept (i : Fin 15) (hi : i ≠ 1) : D.R (r i) = S.R (r i) :=
    Function.update_of_ne (r.injective.ne hi) _ _
  obtain ⟨w,E,m,mark,empty,rotate,hm',hu',_,_,frame,rep'⟩ :=
    fiberProgram_exec body (arithmeticPorts.trans r) call slot H c (x/stride%M) M hc (Nat.mod_lt _ pm) hm u D
      ((kept 0 (by decide)).trans coef) (by change D.R (r 1) = _; simp [D]) ((kept 2 (by decide)).trans modulus)
      (fun i hi hj => (kept (arithmeticPorts i) (by intro eqn; have e := congrArg Fin.val eqn; change i.val = 1 at e; omega)).trans
        (blank _ (by change 1 ≤ i.val; omega) (by change i.val ≤ 12; omega) (by intro eqn; have e := congrArg Fin.val eqn; change i.val = 2 at e; omega)))
      marker source dest p q blocks bs ms (by
        intro i j
        simpa [D,Function.comp_apply,Function.update_of_ne (outside 1 (by decide) i)] using rep i j)
      B hB hlen hw hb hv cb cm
  have same (i : Fin 15) (hi : i ≠ 3) := (frame _ (outside i hi)).2
  obtain ⟨w',hw',_,erase⟩ := bclear_exec body (r 1) w E
  have len : (E.R (r 1)).length = H := by simp [same 1 (by decide),D,length_binSyms]
  rw [len] at erase
  let G : Stacks T A := {E with R := Function.update E.R (r 1) []}
  have old (i : Fin 15) (hi : i ≠ 1) (hj : i ≠ 3) : G.R (r i) = S.R (r i) := by
    simpa [G,Function.update_of_ne (r.injective.ne hi)] using (same i hj).trans (kept i hi)
  obtain ⟨z,hz,inc⟩ := countIter_exec body (r.injective.ne (by decide : (13 : Fin 15) ≠ 4)) (r 12)
    w' G ((old 13 (by decide) (by decide)).trans prefixWord)
    ((old 4 (by decide) (by decide)).trans (blank 4 (by decide) (by decide) (by decide)))
  refine ⟨z,_,_,hz.trans (hw'.trans (hu'.trans hu)),?_,Exec.seq get (Exec.seq rotate (Exec.seq erase inc)),
    by simp,?_,mark,?_,?_⟩
  · nlinarith only [hn,hm']
  · simpa [G,Function.update_of_ne (outside 13 (by decide) 8),Function.update_of_ne (outside 1 (by decide) 8)] using empty
  · intro j hj h13
    obtain ⟨hl,hr⟩ := frame j hj
    refine ⟨?_,hl⟩
    by_cases h : j = r 1
    · subst j; simp [G,r.injective.eq_iff,blank 1 (by decide) (by decide) (by decide)]
    · simpa [G,D,Function.update_of_ne h13,Function.update_of_ne h] using hr
  · intro i j
    simpa [G,Function.comp_apply,Function.update_of_ne (outside 13 (by decide) i),
      Function.update_of_ne (outside 1 (by decide) i)] using rep' i j

end IntegerMultBounds.MathlibTM2.Cover.Fallback
