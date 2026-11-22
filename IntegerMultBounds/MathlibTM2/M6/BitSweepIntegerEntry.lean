module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInit
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove
public import IntegerMultBounds.MathlibTM2.Cover.FallbackProjectorEntries

/-! Write fixed signed matrix entries at a tape-supplied modulus and bit width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Cover.Fallback RingFormula Host Stack Node Cover.LabelTraversal

def sweepNatFormula (n : ℕ) : RingFormula Empty :=
  if h : n = 0 then .zero else
    let twice := RingFormula.mul (.sub .one (.sub .zero .one)) (sweepNatFormula (n/2))
    if n%2 = 0 then twice else .sub twice (.sub .zero .one)
termination_by n
decreasing_by omega

theorem sweepNatFormula_eval {R : Type} [CommRing R] (n : ℕ) :
    eval (Empty.elim : Empty → R) (sweepNatFormula n) = n := by
  rw [sweepNatFormula]
  split
  · subst n; simp [eval]
  · have ih := sweepNatFormula_eval (R := R) (n/2)
    split
    · have eqn : n = 2*(n/2) := by omega
      simp only [eval,ih]; conv_rhs => rw [eqn,Nat.cast_mul,Nat.cast_ofNat]
      ring
    · have eqn : n = 2*(n/2)+1 := by omega
      simp only [eval,ih]; conv_rhs => rw [eqn,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      ring
termination_by n
decreasing_by omega

def sweepIntFormula : ℤ → RingFormula Empty
  | .ofNat n => sweepNatFormula n
  | .negSucc n => .sub .zero (sweepNatFormula (n+1))

theorem sweepIntFormula_eval {R : Type} [CommRing R] (z : ℤ) :
    eval (Empty.elim : Empty → R) (sweepIntFormula z) = z := by
  cases z <;> simp [sweepIntFormula,eval,sweepNatFormula_eval,Int.cast_negSucc]

def literalSource (r : Fin 6 ↪ Fin T) : Leaf Empty → Fin T
  | .zero => r 0
  | .one => r 1
  | .input a => a.elim

theorem sweepIntEntry_writes {P U : Type} {T Q A D M : ℕ} [NeZero M] (body : P → Pr P T Q A U)
    (pool : Fin ((D+1)*13) ↪ Fin T) (r : Fin 6 ↪ Fin T) (outside : ∀ i j, r i ≠ pool j)
    (out : Fin T) (outOff : ∀ i, r i ≠ out) (z : ℤ) (depth : (sweepIntFormula z).depth ≤ D)
    (H : ℕ) (fits : M < 2^H) :
    let ok := fun (R : Regs T A) => R (r 0) = binSyms H 0 ∧ R (r 1) = binSyms H (1 : ZMod M).val ∧
      R (r 2) = binSyms H M ∧ (∀ i : Fin 6, 3 ≤ i → R (r i) = []) ∧ ∀ j, R (pool j) = []
    let leaf := fun a dst => bcopy (literalSource r a) dst (r 4) (r 5)
    let f := sweepIntFormula z
    let program := compile leaf (registerBank pool) f 0 (r 3)
    Writes body ok out (.seq ((initFrames pool (r 2) (D+1)).seq (program.seq (clearFrames pool (D+1))))
      (moveRightOrdered (r 3) (r 4) out)) (binSyms H (z : ZMod M).val)
      ((D+1)*(6*H+6)+1+(time H (fun _ => 6*H+6) f+((D+1)*(2*H+2)+1))+(4*H+4)) := by
  intro ok leaf f program v S ⟨zeroWord,oneWord,modulus,free,blank⟩
  let read : Empty → ZMod M := Empty.elim
  let ready := fun (a : Leaf Empty) (dst : Fin T) (R : Regs T A) =>
    [literalSource r a,dst,r 4,r 5].Nodup ∧ R (literalSource r a) = binSyms H (a.value read).val ∧
    R (r 4) = [] ∧ R (r 5) = []
  have writer (a dst) : Writes body (ready a dst) dst (leaf a dst) (binSyms H (a.value read).val) (6*H+6) := by
    intro u B ⟨ports,word,h₄,h₅⟩
    obtain ⟨y,hy,run⟩ := bcopy_exec body ports u B h₄ h₅
    rw [word,length_binSyms] at run
    exact ⟨y,_,hy,le_rfl,run⟩
  obtain ⟨u,k,hu,hk,run⟩ := withFrames_exec body pool (r 2) (r 3) (outside 2) (outside 3) program
    (binSyms H (eval read f).val) _ v S blank (by
      intro y B keep filled scratch
      apply compile_writes (registerBank pool) read H ready body fits leaf (fun _ => 6*H+6) writer f 0 (r 3) y B
      let allowed := fun dst => ∀ i : Fin 6, i ≠ 3 → r i ≠ dst
      apply layout_prepared pool read H ready B.R f 0 (r 3) (by simpa [f] using depth)
        ((keep _ (outside 3)).trans (free _ (by decide))) (fun _ _ _ _ => (outside _ _).symm)
        (fun k _ hk => (filled k hk).trans modulus) (fun k _ => scratch k) allowed
        (fun _ hi => r.injective.ne hi) (fun _ _ _ _ i _ => outside i _)
      · intro a dst hd
        have slot i := keep (r i) (outside i)
        cases a with
        | input i => exact i.elim
        | zero | one =>
          refine ⟨?_,?_,(slot 4).trans (free 4 (by decide)),(slot 5).trans (free 5 (by decide))⟩
          · simp [literalSource,List.nodup_cons,hd 0 (by decide),hd 1 (by decide),Ne.symm (hd 4 (by decide)),Ne.symm (hd 5 (by decide))]
          · first | simpa [Leaf.value,literalSource] using (slot 0).trans zeroWord | exact (slot 1).trans oneWord
      · intro a dst k xs R hd h
        obtain ⟨ports,word,h₄,h₅⟩ := h
        have same i := Function.update_of_ne (f := R) (outside i (finProdFinEquiv (⟨k%(D+1),Nat.mod_lt _ (by omega)⟩, (0 : Fin 13)))) xs
        cases a with
        | input i => exact i.elim
        | zero | one => exact ⟨ports,(same _).trans word,(same 4).trans h₄,(same 5).trans h₅⟩)
  have value : eval read f = (z : ZMod M) := sweepIntFormula_eval z
  have empty := free 3 (by decide)
  rw [value,empty,List.append_nil] at run
  let B := {S with R := Function.update S.R (r 3) (binSyms H (z : ZMod M).val)}
  obtain ⟨y,hy,move⟩ := moveRightOrdered_exec (body := body) (r 3) (r 4) out (by simp) (outOff 3) (outOff 4)
    u B (by simpa [B] using free 4 (by decide))
  rw [modulus,length_binSyms] at hk
  refine ⟨y,k+(4*(B.R (r 3)).length+4),hy.trans hu,by simpa [B,length_binSyms] using Nat.add_le_add_right hk (4*H+4),Exec.seq run ?_⟩
  simpa only [B,Function.update_self,Function.update_idem,Function.update_of_ne (outOff 3).symm,
    ← empty,Function.update_eq_self] using move

theorem sweepIntMatrix_writes {P U : Type} {T Q A D M d e : ℕ} [NeZero M] (body : P → Pr P T Q A U)
    (pool : Fin ((D+1)*13) ↪ Fin T) (r : Fin 6 ↪ Fin T) (outside : ∀ i j, r i ≠ pool j)
    (out : Fin T) (outOff : ∀ i, r i ≠ out) (poolOff : ∀ j, pool j ≠ out)
    (mat : Matrix (Fin d) (Fin e) ℤ) (depth : ∀ i j, (sweepIntFormula (mat i j)).depth ≤ D)
    (H : ℕ) (fits : M < 2^H) :
    let ok := fun (R : Regs T A) => R (r 0) = binSyms H 0 ∧ R (r 1) = binSyms H (1 : ZMod M).val ∧
      R (r 2) = binSyms H M ∧ (∀ i : Fin 6, 3 ≤ i → R (r i) = []) ∧ ∀ j, R (pool j) = []
    let cost := fun i j => time H (fun _ => 6*H+6) (sweepIntFormula (mat i j))
    let bound := Finset.univ.sup fun i => Finset.univ.sup (cost i)
    let leaf := fun a dst => bcopy (literalSource r a) dst (r 4) (r 5)
    let entry := fun i j => compile leaf (registerBank pool) (sweepIntFormula (mat i j)) 0 (r 3)
    let emit := fun i j => .seq ((initFrames pool (r 2) (D+1)).seq ((entry i j).seq (clearFrames pool (D+1))))
      (moveRightOrdered (r 3) (r 4) out)
    Writes body ok out (sequence (fun i => sequence (emit i) (List.finRange e)) (List.finRange d))
      (matrixWords A H (fun i j => (mat i j : ZMod M))) (d*(e*((D+1)*(6*H+6)+1+
        (bound+((D+1)*(2*H+2)+1))+(4*H+4))+1)+1) := by
  intro ok cost bound leaf entry emit
  apply matrixWords_writes
  · intro R xs h
    simpa only [ok,Function.update_of_ne (outOff _),Function.update_of_ne (poolOff _)] using h
  · intro i j v S ready
    obtain ⟨u,n,hu,hn,run⟩ := sweepIntEntry_writes body pool r outside out outOff (mat i j) (depth i j) H fits v S ready
    have cap : cost i j ≤ bound := (Finset.le_sup (f := cost i) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun k => Finset.univ.sup (cost k)) (Finset.mem_univ i))
    change n ≤ (D+1)*(6*H+6)+1+(cost i j+((D+1)*(2*H+2)+1))+(4*H+4) at hn
    exact ⟨u,n,hu,by omega,run⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
