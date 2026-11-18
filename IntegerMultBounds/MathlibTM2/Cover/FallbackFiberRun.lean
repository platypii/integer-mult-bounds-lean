module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberInput
public import IntegerMultBounds.MathlibTM2.Host.Embed
import IntegerMultBounds.MathlibTM2.Routing.BinaryCeilLogData

/-! Execute a modular row addition on a single represented fiber. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host TranslationExecutionReuse
variable {T A : ℕ} {P U : Type}

/-- Erase the descriptor, including any explicit blank padding left by simulation. -/
def resetOffset (i : Fin T) : Pr P T 217 A U :=
  .seq (unload i) (.seq (bclear i) (.act (.push (.lt i) (fun _ => separator) .done)))

private theorem reset_exec (body : P → Pr P T 217 A U) (i : Fin T) (v : HS T 217 A U)
    (S : Stacks T A) :
    ∃ z n, z.user = v.user ∧ n ≤ 4*((S.L i).length+(S.R i).length)+5 ∧
      Exec body (resetOffset i) (mk v S) n (mk z {S with
        L := Function.update S.L i [separator], R := Function.update S.R i []}) := by
  obtain ⟨u,hu,he⟩ := unload_exec body i v S
  let D : Stacks T A := {S with
    L := Function.update S.L i []
    R := Function.update S.R i ((S.L i).reverse ++ S.R i)}
  obtain ⟨z,hz,_,hc⟩ := bclear_exec body i u D
  let F := {D with R := Function.update D.R i []}
  have hp := Exec.act (body := body) (.push (.lt i) (fun _ => separator) .done) (mk z F)
  refine ⟨z,2*(S.L i).length+2+(2*(D.R i).length+2+1),hz.trans hu,?_,Exec.seq he (Exec.seq hc ?_)⟩
  · simp [D]; omega
  · simpa [F,D,Action.run,update_lt,store_mk] using hp

def fiberProgram (r : Fin 13 ↪ Fin T) (call : Fin 12 ↪ Fin T) : Pr P T 217 A U :=
  .seq (.seq (offsetProgram r) (embProg call Empty.elim
    (foreign (Alphabet.program RadixToBinary.binaryEncoding program)))) (resetOffset (call 8))

theorem fiberProgram_exec (body : P → Pr P T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (L c x M : ℕ) (hc : c < M) (hx : x < M) (hM : M < 2^L)
    (v : HS T 217 A U) (S : Stacks T A) (hcoef : S.R (r 0) = binSyms L c)
    (hdigit : S.R (r 1) = binSyms L x) (hmod : S.R (r 2) = binSyms L M)
    (hblank : ∀ i : Fin 13, 3 ≤ i → i < 12 → S.R (r i) = [])
    (marker : S.L (r 3) = [separator])
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4))) (bs ms : List Bool)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (input source dest p q blocks bs ms [])) (S.L ∘ call) (S.R ∘ call))
    (B : ℕ) (hB : 0 < B) (hlen : blocks.length = M) (hw : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms) :
    ∃ z F n, F.L (call 8) = [separator] ∧ F.R (call 8) = [] ∧
      Exec body (fiberProgram r call) (mk v S) n (mk z F) ∧
      n ≤ 48*L*L+158*L+85 + (207*(M*B)+241)*25 ∧
      z.user = v.user ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ j, (∀ i, call i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (output M (c*x % M) B source dest p q blocks bs ms [])) (F.L ∘ call) (F.R ∘ call) := by
  obtain ⟨offset,v₁,n₁,co,hv,hu₁,hn₁,he₁,hr⟩ :=
    fiberInput_exec body r call slot L c x M hc hx hM v S hcoef hdigit hmod hblank marker
      source dest p q blocks bs ms rep
  let D : Stacks T A := {S with R := Function.update S.R (r 3) (offset.map bitSymbol)}
  let enc := RadixToBinary.binaryEncoding (q := A)
  let w := input source dest p q blocks bs ms offset
  let w' := output M (c*x % M) B source dest p q blocks bs ms offset
  have ht := Alphabet.map_hoare enc (translate_hoare M _ B
    (Nat.mod_lt _ (Nat.zero_lt_of_lt hx)).le hB source dest p q blocks hlen hw bs ms offset hb hm hv cb cm co)
  have run : HoareTime (Alphabet.program enc program) (· = Alphabet.mapTapes enc w)
      (· = Alphabet.mapTapes enc w') (207*(M*B)+241) := by
    apply ht.consequence _ _ le_rfl
    · rintro _ rfl; exact ⟨_,rfl,rfl⟩
    · rintro _ ⟨_,rfl,rfl⟩; rfl
  obtain ⟨u,G,_,rfl,hrep,hu,hi,ho,hsize,n₂,hn₂,he₂⟩ := foreign_exec
    (P := Empty) Empty.elim _ run (embDn call v₁) (embStk call D) _ rfl hr
  obtain ⟨z,F,he,_,hz,hF,frame⟩ := exec_emb (body' := body) (ι := Empty.elim)
    call.injective (fun e => nomatch e) he₂ v₁ rfl D rfl
  obtain ⟨z',n₃,hz',hn₃,reset⟩ := reset_exec body (call 8) z F
  have size := hsize 8
  rw [← hF] at size
  change (F.L (call 8)).length + (F.R (call 8)).length ≤
    (D.L (call 8)).length + (D.R (call 8)).length + _ at size
  simp only [D,slot,marker,List.length_singleton,Function.update_self,List.length_map] at size
  have bits : offset.length ≤ L := by
    rw [Routing.canonicalBinary_length_clog offset co,hv]
    exact Nat.clog_le_of_le_pow (Nat.succ_le_of_lt ((Nat.mod_lt _ (Nat.zero_lt_of_lt hx)).trans hM))
  rw [slot] at hn₃
  refine ⟨z',_,_,by simp,by simp,Exec.seq (Exec.seq he₁ he) reset,by omega,
    hz'.trans (hz.trans (hu.trans hu₁)),?_,?_,?_,?_⟩
  · exact (congrArg Stacks.inp hF).trans hi
  · exact (congrArg Stacks.out hF).trans ho
  · intro j hj
    simpa [Function.update_of_ne (hj 8).symm,D,Function.update_of_ne ((slot ▸ hj 8).symm)] using frame j hj
  · rw [← hF] at hrep
    intro i k
    by_cases h : i = 8
    · subst i
      change RadixZeroFill.encodedBinary [] k = readAt blank (Function.update F.L (call 8) _ (call 8))
        (Function.update F.R (call 8) _ (call 8)) (k-1)
      rw [Function.update_self,Function.update_self,readAt_single,encodedBinary_eq]; rfl
    · have ne := call.injective.ne h
      have eqs : (w'.tape i = (output M (c*x%M) B source dest p q blocks bs ms []).tape i) ∧
          (w'.head i = (output M (c*x%M) B source dest p q blocks bs ms []).head i) := by
        fin_cases i <;> first | exact ⟨rfl,rfl⟩ | contradiction
      simpa only [Alphabet.mapTapes,Function.comp_apply,embStk,Function.update_of_ne ne,
        eqs.1,eqs.2] using hrep i k

end IntegerMultBounds.MathlibTM2.Cover.Fallback
