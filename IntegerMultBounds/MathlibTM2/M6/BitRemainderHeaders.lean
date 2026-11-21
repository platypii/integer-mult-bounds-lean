module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordVolumeHeaders
public import IntegerMultBounds.MathlibTM2.Cover.LabelTraversal

/-! Compute the six dimension words for the normalized rank child of a PR589 idle record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.IntervalDescriptor
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Cover Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
variable {T Q : ℕ} {P U : Type}

private theorem sequenceHeaders_exec {k : ℕ} (body : P → Pr P T Q prime U)
    (program : Fin k → Pr P T Q prime U) (dst : Fin k ↪ Fin T) (word : Fin k → List (Fin (prime+4)))
    (cost : Fin k → ℕ) (ok : (Fin T → List (Fin (prime+4))) → Prop)
    (stable : ∀ R F, ok R → (∀ i, (∀ j, i ≠ dst j) → F i = R i) → ok F)
    (step : ∀ i u S, ok S.R → S.R (dst i) = [] →
      ∃ z n, z.user = u.user ∧ n ≤ cost i ∧ Exec body (program i) (mk u S) n
        (mk z {S with R := Function.update S.R (dst i) (word i)}))
    (is : List (Fin k)) (unique : is.Nodup) (u : HS T Q prime U) (S : Stacks T prime)
    (valid : ok S.R) (empty : ∀ i ∈ is, S.R (dst i) = []) :
    ∃ z D n, z.user = u.user ∧ n ≤ (is.map cost).sum+1 ∧
      Exec body (LabelTraversal.sequence program is) (mk u S) n (mk z D) ∧ D.L = S.L ∧
      (∀ i ∈ is, D.R (dst i) = word i) ∧ (∀ j, (∀ i ∈ is, j ≠ dst i) → D.R j = S.R j) := by
  induction is with
  | nil =>
    exact ⟨u,S,1,rfl,by simp,by simpa [LabelTraversal.sequence,Action.run] using
      (Exec.act (body := body) (.done : Act T Q prime U) (mk u S)),rfl,by simp,by simp⟩
  | cons i is ih =>
    obtain ⟨outside,rest⟩ := List.nodup_cons.mp unique
    obtain ⟨y,B,t,yu,time,run,left,done,frame⟩ := ih rest (fun j hj => empty j (by simp [hj]))
    have fresh := frame (dst i) (fun j hj => dst.injective.ne (fun eq => outside (eq ▸ hj)))
    obtain ⟨z,n,zy,price,write⟩ := step i y B (stable _ _ valid (fun j off => frame j (fun l _ => off l)))
      (fresh.trans (empty i (by simp)))
    refine ⟨z,_,_,zy.trans yu,by simp only [List.map_cons,List.sum_cons]; omega,Exec.seq run write,left,?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Function.update_self ..
      · exact (Function.update_of_ne (dst.injective.ne (show j ≠ i from fun eq => outside (eq ▸ hj))) ..).trans (done j hj)
    · intro j off
      exact (Function.update_of_ne (off i (by simp)) ..).trans (frame j (fun l hl => off l (by simp [hl])))

/-- Save the three outer directory dimensions before the record scanner
reuses their unary source tapes. All conversions share six scratch tapes. -/
def directoryOuterHeaders {A : ℕ} (bank : Fin 12 ↪ Fin T) : Pr P T Q A U :=
  LabelTraversal.sequence (fun i : Fin 3 => unaryBinary
    (bank (i.castAdd 9)) (bank ((i.natAdd 3).castAdd 6))
    (bank 6) (bank 7) (bank 8) (bank 9) (bank 10) (bank 11)) (List.finRange 3)

theorem directoryOuterHeaders_exec (body : P → Pr P T Q prime U) (bank : Fin 12 ↪ Fin T)
    (value : Fin 3 → ℕ) (u : HS T Q prime U) (S : Stacks T prime)
    (source : ∀ i : Fin 3, (S.R (bank (i.castAdd 9))).length = value i)
    (empty : ∀ i : Fin 12, 3 ≤ i.val → S.R (bank i) = []) :
    let dst := ((Fin.natAddEmb (m := 3) 3).trans (Fin.castAddEmb 6)).trans bank
    ∃ z D n, z.user = u.user ∧ n ≤ 21*(value 0+value 1+value 2)+31 ∧
      Exec body (directoryOuterHeaders bank) (mk u S) n (mk z D) ∧ D.L = S.L ∧
      (∀ i, D.R (dst i) = binSyms (value i).size (value i)) ∧
      ∀ k, (∀ i, k ≠ dst i) → D.R k = S.R k := by
  intro dst
  let ok := fun R : Fin T → List (Fin (prime+4)) =>
    (∀ i : Fin 3, (R (bank (i.castAdd 9))).length = value i) ∧
    ∀ i : Fin 12, 6 ≤ i.val → R (bank i) = []
  have off (i : Fin 12) (outside : i.val < 3 ∨ 6 ≤ i.val) (j : Fin 3) : bank i ≠ dst j :=
    bank.injective.ne (by intro eq; have h := congrArg Fin.val eq; change i.val = 3+j.val at h; omega)
  have stable (R F) (h : ok R) (keep : ∀ k, (∀ i, k ≠ dst i) → F k = R k) : ok F := by
    constructor
    · intro i
      rw [keep _ (off _ (Or.inl i.isLt))]
      exact h.1 i
    · intro i hi
      exact (keep _ (off i (Or.inr hi))).trans (h.2 i hi)
  let program : Fin 3 → Pr P T Q prime U := fun i => unaryBinary (bank (i.castAdd 9)) (dst i)
    (bank 6) (bank 7) (bank 8) (bank 9) (bank 10) (bank 11)
  have step (i : Fin 3) (a : HS T Q prime U) (A : Stacks T prime) (h : ok A.R) (fresh : A.R (dst i) = []) :
      ∃ z n, z.user = a.user ∧ n ≤ 21*value i+10 ∧ Exec body (program i) (mk a A) n
        (mk z {A with R := Function.update A.R (dst i) (binSyms (value i).size (value i))}) := by
    refine unaryBinary_exec (body := body)
      (((by decide : ∀ i : Fin 3, [i.castAdd 9,(i.natAdd 3).castAdd 6,6,7,8,9,10,11].Nodup) i).map bank.injective)
      _ a A (h.1 i) ?_
    · intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact fresh
      all_goals exact h.2 _ (by decide)

  obtain ⟨z,D,n,user,price,run,left,outputs,frame⟩ := sequenceHeaders_exec body program dst
    (fun i => binSyms (value i).size (value i)) (fun i => 21*value i+10) ok stable step (List.finRange 3)
    (List.nodup_finRange _) u S ⟨source,fun i hi => empty i (by omega)⟩
    (fun i _ => empty _ (by change 3 ≤ 3+i.val; omega))
  have indices : List.finRange 3 = [0,1,2] := by decide
  rw [indices] at price
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at price
  exact ⟨z,D,n,user,by omega,run,left,fun i => outputs i (by simp),fun k h => frame k (fun i _ => h i)⟩

def descriptorPorts : Fin 6 ↪ Fin 72 := (Fin.natAddEmb 33).trans (Fin.castLEEmb (by decide))

def powerPorts (i : Fin 3) : Fin 10 ↪ Fin 72 :=
  ⟨![2,if i = 2 then 53 else 28,(![35,37,38] : Fin 3 → Fin 72) i,59,60,61,62,63,64,65],
    by fin_cases i <;> decide⟩

def widthPorts : Fin 9 ↪ Fin 72 := ⟨![71,36,59,60,61,62,63,64,65],by decide⟩

/-- Convert the unary product of interval rank and atom width into the width header. -/
noncomputable def intervalWidth (r : Fin 9 ↪ Fin T) (rank : ℕ) : Pr P T Q prime U :=
  (Node.umul rank (r 0) (r 8) (r 2)).seq
    ((unaryBinary (r 8) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7)).seq (bclear (r 8)))

private theorem intervalWidth_exec (body : P → Pr P T Q prime U) (r : Fin 9 ↪ Fin T) (rank a : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) (atom : (S.R (r 0)).length = a)
    (empty : ∀ i : Fin 9, i ≠ 0 → S.R (r i) = []) :
    ∃ z n, z.user = u.user ∧ n ≤ 4*a+4 + (21*(rank*a)+10 + (2*(rank*a)+2)) ∧
      Exec body (intervalWidth r rank) (mk u S) n (mk z {S with R := Function.update S.R (r 1) ((bits (rank*a)).map bitSymbol)}) := by
  obtain ⟨y,yu,mul⟩ := Node.umulSym_exec body rank Node.tick (a := r 0) (b := r 8) (t := r 2)
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide)) u S (empty 2 (by decide))
  rw [atom,empty 8 (by decide),List.append_nil] at mul
  let tally := List.replicate (rank*a) (Node.tick (A := prime))
  let B := {S with R := Function.update S.R (r 8) tally}
  obtain ⟨z,n,zy,price,binary⟩ := unaryBinary_exec (body := body)
    ((by decide : ([8,1,2,3,4,5,6,7] : List (Fin 9)).Nodup).map r.injective) (rank*a) y B
    (by simp [B,tally]) (by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (show j ∈ ([1,2,3,4,5,6,7] : List (Fin 9)).map r from hj)
      have ne := (by decide : ∀ i ∈ ([1,2,3,4,5,6,7] : List (Fin 9)), i ≠ 8 ∧ i ≠ 0) i hi
      exact (Function.update_of_ne (r.injective.ne ne.1) ..).trans (empty i ne.2))
  let D := {B with R := Function.update B.R (r 1) (binSyms (rank*a).size (rank*a))}
  obtain ⟨v,vz,_,clear⟩ := bclear_exec body (r 8) z D
  have len : (D.R (r 8)).length = rank*a := by simp [D,B,tally,r.injective.eq_iff]
  rw [len] at clear
  refine ⟨v,_,vz.trans (zy.trans yu),Nat.add_le_add_left (Nat.add_le_add_right price _) _,?_⟩
  apply (Exec.seq mul (Exec.seq binary clear)).cast rfl
  congr 2
  funext i
  by_cases saved : i = r 8
  · subst i; simp [D,B,r.injective.eq_iff,empty]
  · by_cases out : i = r 1
    · subst i; simp [D,B,r.injective.eq_iff,canonicalBits_symbols]
    · simp [D,B,Function.update_of_ne saved,Function.update_of_ne out]

noncomputable def fieldPrograms (bank : Fin 72 ↪ Fin T) (lo hi : ℕ) : Fin 6 → Pr P T Q prime U :=
  ![.act (pushBit (bank 33) true),.act (pushBit (bank 34) true),
    .act (pushBit (bank 35) true),intervalWidth (widthPorts.trans bank) (hi-lo),
    swapPrefix ((powerPorts 1).trans bank) (2*(64-(hi-lo))),swapPrefix ((powerPorts 2).trans bank) 0]

noncomputable def intervalHeaders (bank : Fin 72 ↪ Fin T) (lo hi : ℕ) : Pr P T Q prime U :=
  LabelTraversal.sequence (fieldPrograms bank lo hi) (List.finRange 6)

def intervalValues (lo hi a M W : ℕ) : Fin 6 → ℕ :=
  ![1,1,1,(hi-lo)*a,M^(2*(64-(hi-lo))),W]

def intervalHeaderCosts (lo hi a H J : ℕ) : Fin 6 → ℕ :=
  let power := fun d B => dimensionTime H B d + (4*(d*H+B)+6)
  ![1,1,1,4*a+4+(21*((hi-lo)*a)+10+(2*((hi-lo)*a)+2)),power (2*(64-(hi-lo))) 1,power 0 J]

/-- Generate every descriptor field from the modulus, suffix and atom width.
The indexed program depends only on the selected interval. -/
theorem intervalHeaders_exec (body : P → Pr P T Q prime U) (bank : Fin 72 ↪ Fin T)
    (lo hi a H J M W : ℕ) (hm : M < 2^H) (hw : W < 2^J) (u : HS T Q prime U) (S : Stacks T prime)
    (base : S.R (bank 2) = binSyms H M) (unit : S.R (bank 28) = binSyms 1 1)
    (suffix : S.R (bank 53) = binSyms J W) (atom : (S.R (bank 71)).length = a)
    (scratch : ∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = [])
    (empty : ∀ i, S.R (bank (descriptorPorts i)) = []) :
    ∃ z D t, z.user = u.user ∧ t ≤ ((List.finRange 6).map (intervalHeaderCosts lo hi a H J)).sum+1 ∧
      Exec body (intervalHeaders bank lo hi) (mk u S) t (mk z D) ∧ D.L = S.L ∧
      (∀ i, D.R (bank (descriptorPorts i)) = (bits (intervalValues lo hi a M W i)).map bitSymbol) ∧
      ∀ k, (∀ i, k ≠ bank (descriptorPorts i)) → D.R k = S.R k := by
  let dst := descriptorPorts.trans bank
  let ok := fun (R : Fin T → List (Fin (prime+4))) => R (bank 2) = binSyms H M ∧ R (bank 28) = binSyms 1 1 ∧
    R (bank 53) = binSyms J W ∧ (R (bank 71)).length = a ∧ ∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → R (bank i) = []
  have stable (R F) (h : ok R) (frame : ∀ k, (∀ i, k ≠ dst i) → F k = R k) : ok F := by
    have keep (i : Fin 72) (outside : i.val < 33 ∨ 38 < i.val) : F (bank i) = R (bank i) := by
      apply frame
      intro j
      apply bank.injective.ne
      intro eq
      have bounds := (by decide : ∀ j, 33 ≤ (descriptorPorts j).val ∧ (descriptorPorts j).val ≤ 38) j
      have same := congrArg Fin.val eq
      omega
    exact ⟨(keep 2 (by decide)).trans h.1,(keep 28 (by decide)).trans h.2.1,(keep 53 (by decide)).trans h.2.2.1,
      (congrArg List.length (keep 71 (by decide))).trans h.2.2.2.1,fun i low high => (keep i (by omega)).trans (h.2.2.2.2 i low high)⟩
  have step (i : Fin 6) (y : HS T Q prime U) (B : Stacks T prime) (h : ok B.R) (fresh : B.R (dst i) = []) :
      ∃ z n, z.user = y.user ∧ n ≤ intervalHeaderCosts lo hi a H J i ∧
        Exec body (fieldPrograms bank lo hi i) (mk y B) n (mk z {B with R := Function.update B.R (dst i) ((bits (intervalValues lo hi a M W i)).map bitSymbol)}) := by
    obtain ⟨base,one,trailing,clock,work⟩ := h
    have power (j : Fin 3) (d L b : ℕ) (hb : b < 2^L)
        (seed : B.R (bank (powerPorts j 1)) = binSyms L b) (out : B.R (bank (powerPorts j 2)) = []) :=
      scaledPrefix_exec body ((powerPorts j).trans bank) d H L M b hm hb y B
        (by have eq := (by decide : ∀ j, powerPorts j 0 = 2) j; exact (congrArg (B.R ∘ bank) eq).trans base) seed (by
          intro k low high
          by_cases atOut : k = 2
          · exact atOut ▸ out
          · have limits := (by decide : ∀ j k, 2 ≤ k → k < 9 → k ≠ 2 →
                59 ≤ (powerPorts j k).val ∧ (powerPorts j k).val ≤ 65) j k low high atOut
            exact work _ limits.1 limits.2)
    have short (k : Fin T) (e : B.R k = []) :
        Exec body (.act (pushBit k true)) (mk y B) 1 (mk y {B with R := Function.update B.R k ((bits 1).map bitSymbol)}) := by
      have run := Exec.act (body := body) (pushBit k true) (mk y B)
      rw [pushBit_run,e] at run
      exact run
    fin_cases i
    · exact ⟨y,1,rfl,le_rfl,short _ fresh⟩
    · exact ⟨y,1,rfl,le_rfl,short _ fresh⟩
    · exact ⟨y,1,rfl,le_rfl,short _ fresh⟩
    · apply intervalWidth_exec body (widthPorts.trans bank) (hi-lo) a y B clock
      intro j ne
      by_cases atOut : j = 1
      · exact atOut ▸ fresh
      · have limits := (by decide : ∀ j, j ≠ 0 → j ≠ 1 → 59 ≤ (widthPorts j).val ∧ (widthPorts j).val ≤ 65) j ne atOut
        exact work _ limits.1 limits.2
    · have run := power 1 (2*(64-(hi-lo))) 1 1 (by decide) one fresh
      rw [Nat.mul_one] at run
      exact run
    · have run := power 2 0 J W hw trailing fresh
      rw [pow_zero,one_mul] at run
      exact run
  obtain ⟨z,D,t,user,time,run,left,done,frame⟩ := sequenceHeaders_exec body _ dst _ _ ok stable step
    (List.finRange 6) (List.nodup_finRange _) u S ⟨base,unit,suffix,atom,scratch⟩ (fun i _ => empty i)
  exact ⟨z,D,t,user,time,run,left,fun i => done i (List.mem_finRange _),fun k off => frame k (fun j _ => off j)⟩

private theorem powerHeaderCost_le (d H B M W : ℕ) (degree : d ≤ 128) (width : H ≤ M)
    (seed : B ≤ W) (radix : 1 ≤ M) (positive : 1 ≤ W) :
    dimensionTime H B d + (4*(d*H+B)+6) ≤ 1000000*(M*M*W) := by
  have m2 : M ≤ M*M := Nat.le_mul_of_pos_right _ radix
  have weight : M*M ≤ M*M*W := Nat.le_mul_of_pos_right _ positive
  have cross : M*W ≤ M*M*W := Nat.mul_le_mul_right W m2
  have tail : W ≤ M*W := Nat.le_mul_of_pos_left _ radix
  calc
    _ ≤ 6*B+6+d*((12*H+18)*(d*H+B)+20*H+26)+(4*(d*H+B)+6) :=
      Nat.add_le_add_right (dimensionTime_le ..) _
    _ ≤ 6*W+6+128*((12*M+18)*(128*M+W)+20*M+26)+(4*(128*M+W)+6) := by gcongr
    _ ≤ _ := by nlinarith only [m2,weight,cross,tail,radix]

/-- All six header writes fit in one parent-volume unit after the role split. -/
theorem intervalHeaderCost_le (lo hi a H J M W : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64)
    (atom : a ≤ M) (width : H ≤ M) (seed : J ≤ W) (radix : 2 ≤ M) (positive : 0 < W) :
    ((List.finRange 6).map (intervalHeaderCosts lo hi a H J)).sum+1 ≤ M^64*W := by
  let C := M*M*W
  have m2 : M ≤ M*M := Nat.le_mul_of_pos_right _ (by omega)
  have weight : M*M ≤ C := Nat.le_mul_of_pos_right _ positive
  have unit : 1 ≤ W := positive
  have power (d : ℕ) (degree : d ≤ 128) (B : ℕ) (h : B ≤ W) :=
    powerHeaderCost_le d H B M W degree width h (by omega) positive
  have q := power (2*(64-(hi-lo))) (by omega) 1 unit
  have r := power 0 (by omega) J seed
  have rank : (hi-lo)*a ≤ 64*M := Nat.mul_le_mul (by omega) atom
  change 1+(1+(1+
    ((4*a+4+(21*((hi-lo)*a)+10+(2*((hi-lo)*a)+2)))+
    ((dimensionTime H 1 (2*(64-(hi-lo)))+(4*((2*(64-(hi-lo)))*H+1)+6))+
    ((dimensionTime H J 0+(4*(0*H+J)+6))+0)))))+1 ≤ _
  calc
    _ ≤ 4194304*C := by dsimp only [C] at *; omega
    _ ≤ (M^22)*(M*M*W) := Nat.mul_le_mul_right _ (show 2^22 ≤ M^22 from Nat.pow_le_pow_left radix _)
    _ = M^24*W := by rw [show M^24 = M^22*M^2 from pow_add M 22 2,pow_two]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by decide))

end IntegerMultBounds.MathlibTM2.M6.BitNode.IntervalDescriptor
