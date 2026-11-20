module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinary
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGeneratedGoodRecord

/-! Load the physical ordinary adapter from the directory's current record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks.Shared50ModularControl
open IntegerMultBounds.MathlibTM2.Stack Host Cover Cover.Fallback
open HeadPivotLayout HeadWidthLayout CrossWeightLayout GoodChildLayout

def entrySlot (i : Fin 58) : Fin (66+58) :=
  if i.val ∈ [2,24,28,44,45,53] then i.castLE (by decide)
  else if i = 48 then 55 else Fin.natAdd 66 i

def entrySlots : Fin 58 ↪ Fin (66+58) :=
  ⟨entrySlot,by intro i j; exact (by decide +kernel : ∀ i j, entrySlot i = entrySlot j → i = j) i j⟩

/-- Only the payload, immutable headers and parent weights use directory tapes. -/
def ordinaryCaller {K : ℕ} (room : 58 ≤ K) : Fin 58 ↪ Fin (66+K) :=
  entrySlots.trans (Fin.castLEEmb (Nat.add_le_add_left room 66))

theorem ordinaryEntry_exec {K m w W H J Q : ℕ} {P U : Type} (room : 58 ≤ K)
    (body : P → Pr P (66+K) Q prime U) (v : RecursiveInterchangeLayout.Descriptor)
    (proj : Matrix (Fin m) (Fin m) ℚ) (weights : Fin m → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (schedules : List ℕ → List (Fin (prime+4))) (pending : List ℕ)
    (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime)
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedules S pending)
    (word : Fin ((prime^(w+1))^(m+m)*W) → ZMod 2) :
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩
    let full := ordinaryCaller room
    let bank := adapterBank.trans (parent.trans (parentWithWeights.trans full))
    let coeffs := (coeff true).trans (head.trans bank)
    let ports := entry.trans bank
    let parentWords := (List.ofFn fun i => binSyms (A := prime) H (weights i).val).flatten
    (∀ z, RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
      (List.ofFn (SparseRoleCircuit.encode ∘ word)) z) = readAt blank (S.L (full 24)) (S.R (full 24)) z) →
    ∃ z D, z.user = u.user ∧
      Exec body (bcopy (full 2) (full 33) (full 0) (full 1)) (mk u S) (6*H+6) (mk z D) ∧
      HeadColumnReady (d := m+m) (W := W) coeffs ports H J [] parentWords [] SparseRoleCircuit.encode
        (fun _ => blank) (fun _ => blank) 0 0 word D ∧
      D = {S with R := Function.update S.R (full 33) (binSyms H M)} := by
  intro M full bank coeffs ports parentWords payload
  obtain ⟨_,_,privateBlank,_,_,base,one,width,_,_,_,parentStored,_⟩ := ready
  have privatePort (i : Fin 58) (hi : 58 ≤ (entrySlot i).val) :
      S.L (full i) = [] ∧ S.R (full i) = [] := privateBlank _ hi
  have baseSlot : S.R (full 2) = binSyms H M := base
  obtain ⟨z,user,run⟩ := bcopy_exec (body := body)
    ((by decide : ([2,33,0,1] : List (Fin 58)).Nodup).map full.injective)
    u S (privatePort 0 (by decide)).2 (privatePort 1 (by decide)).2
  simp only [baseSlot,(privatePort 33 (by decide)).2,List.append_nil,length_binSyms] at run
  let D := {S with R := Function.update S.R (full 33) (binSyms H M)}
  have keep (i : Fin 58) (hi : i ≠ 33) : D.R (full i) = S.R (full i) :=
    Function.update_of_ne (full.injective.ne hi) ..
  have free (i : Fin 58) (hi : 58 ≤ (entrySlot i).val) (off : i ≠ 33) :
      D.L (full i) = [] ∧ D.R (full i) = [] := ⟨(privatePort i hi).1,(keep _ off).trans (privatePort i hi).2⟩
  refine ⟨z,D,user,run,?_,rfl⟩
  constructor
  · exact (free 52 (by decide) (by decide)).2
  · exact (keep 48 (by decide)).trans parentStored
  · exact (free 41 (by decide) (by decide)).2
  · exact Function.update_self (full 33) (binSyms H M) S.R
  · intro j hj
    let i := (coeff true j).castLE (by decide : 53 ≤ 58)
    have bounds := (by decide : ∀ j : Fin 17, j ≤ 1 ∨ 3 ≤ j ∧ j ≤ 11 →
      58 ≤ (entrySlot ((coeff true j).castLE (by decide))).val ∧ (coeff true j).val ≠ 33) j hj
    exact (free i bounds.1 (fun eq => bounds.2 (congrArg Fin.val eq))).2
  · exact (keep 2 (by decide)).trans base
  · exact (keep 28 (by decide)).trans one
  · exact (keep 53 (by decide)).trans width
  · intro j hj
    let i := (entry j).castLE (by decide : 54 ≤ 58)
    have bounds := (by decide : ∀ j ∈ headShearWork,
      58 ≤ (entrySlot ((entry j).castLE (by decide))).val ∧ (entry j).val ≠ 33) j hj
    exact free i bounds.1 (fun eq => bounds.2 (congrArg Fin.val eq))
  · intro k
    simpa only [sub_zero,show ports 24 = full 24 from rfl,keep 24 (by decide)] using payload k
  · intro k
    obtain ⟨l,r⟩ := free 25 (by decide) (by decide)
    rw [show ports 25 = full 25 from rfl,l,r,readAt_nil_left,wordTape_nil]
    rfl

def pivotSlots : Fin 23 ↪ Fin 58 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,47,49,50,17,18,19,44,21,45],by decide⟩

private theorem stageBank_swap (r : Fin 23 ↪ Fin T) (n : ℕ) (i : Fin 23) :
    stageBank r n i = r (((Equiv.swap 15 16 : Equiv.Perm (Fin 23))^n) i) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    change stageBank r n (Equiv.swap 15 16 i) = _
    rw [ih,pow_succ]
    rfl

private theorem stageBank_twice (r : Fin 23 ↪ Fin T) (n : ℕ) (i : Fin 23) :
    stageBank (stageBank r n) n i = r i := by
  rw [stageBank_swap,stageBank_swap]
  congr 1
  let σ : Equiv.Perm (Fin 23) := Equiv.swap 15 16
  change (σ^n * σ^n) i = i
  have twice : σ^2 = 1 := by rw [pow_two]; exact Equiv.swap_mul_self _ _
  rw [← pow_add,← two_mul,pow_mul,twice,one_pow]
  rfl

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- Start elimination on the parity-selected matrix tape so that the final archive
and gathered pivot words land directly on adapter tapes 49, 50 and 47. -/
theorem ordinaryArchive_exec {K m w H Q : ℕ} {P U : Type} (room : 58 ≤ K)
    (body : P → Pr P (66+K) Q prime U) (G : Matrix (Fin m) (Fin m) (ZMod (prime^(w+1))))
    (r : ℕ) (hr : r ≤ m) (minor : ∀ k (hk : k < r), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (hm : prime^(w+1) < 2^H) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime) :
    let full := ordinaryCaller room
    let slots := stageBank (pivotSlots.trans full) r
    let words := fun k => if hk : k ≤ r then matrixWords prime H (GoodForm.stageAt G r hr minor k hk).M else []
    let stage := GoodForm.stageAt G r hr minor r le_rfl
    S.R (slots 2) = binSyms H (prime^(w+1)) → S.R (slots 20) = binSyms H (1 : ZMod (prime^(w+1))).val →
    (S.R (slots 22)).length = w →
    (∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (slots i) = []) →
    ∀ tail, S.R (slots 15) = matrixWords prime H G ++ tail →
    ∃ z F n, z.user = u.user ∧ n ≤ r*(4*w+4+columnTime m prime w H)+1+(r*(8*(m*m*H)+14*H+22)+1) ∧
      Exec body (goodWeights prime r hr slots) (mk u S) n (mk z F) ∧
      F.R (full 47) = (List.ofFn fun i : Fin r => binSyms H (stage.M (i.castLE hr) (i.castLE hr)).val).flatten ∧
      (F.R (full 49), F.R (full 50)) = matrixArchive words (S.R (slots 15)) (S.R (slots 16)) r ∧
      F.L = S.L ∧ ∀ j, j ≠ full 47 → j ≠ full 49 → j ≠ full 50 → F.R j = S.R j := by
  intro full slots words stage modulus one ticks free tail matrix
  obtain ⟨z,F,n,user,bill,run,piv,_,archive,left,_,_,off⟩ :=
    goodWeights_exec body slots prime w H prime_prime G hm u S tail matrix modulus one ticks free r hr minor
  have pivot : slots 14 = full 47 := stageBank_fixed _ _ _ (by decide) (by decide)
  have src : stageBank slots r 15 = full 49 := stageBank_twice _ _ _
  have dst : stageBank slots r 16 = full 50 := stageBank_twice _ _ _
  rw [pivot] at piv
  rw [src,dst] at archive
  rw [pivot,src,dst] at off
  exact ⟨z,F,n,user,bill,run,piv,archive,left,off⟩

/-- Transfer a writer's one output to the consumer's tape and restore its
original register, including the case where both placements select the same tape. -/
private theorem forwardWritten_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (src dst tmp : Fin T) (st : src ≠ tmp) (dt : dst ≠ tmp)
    (word : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime)
    (hs : S.R src = []) (hd : S.R dst = []) (ht : S.R tmp = []) :
    ∃ z n, z.user = u.user ∧ n ≤ 4*word.length+4 ∧
      Exec body (if src = dst then .act .done else moveRightOrdered src tmp dst)
        (mk u {S with R := Function.update S.R src word}) n
        (mk z {S with R := Function.update S.R dst word}) := by
  by_cases eq : src = dst
  · subst dst
    exact ⟨u,1,rfl,by omega,by rw [ite_eq_left rfl]; exact Exec.act _ _⟩
  · let B := {S with R := Function.update S.R src word}
    have free : B.R tmp = [] := (Function.update_of_ne st.symm ..).trans ht
    obtain ⟨z,user,run⟩ := moveRightOrdered_exec (body := body) src tmp dst st eq dt.symm u B free
    rw [ite_eq_right eq]
    refine ⟨z,_,user,le_rfl,?_⟩
    have atSrc : B.R src = word := Function.update_self ..
    rw [atSrc] at run
    apply run.cast rfl
    change mk z {S with R := Function.update (Function.update (Function.update S.R src word) src []) dst _} = _
    simp only [B,Function.update_self,Function.update_of_ne (Ne.symm eq),hd,List.append_nil,Function.update_idem]
    rw [← hs,Function.update_eq_self]

private theorem archiveSlots_private (r : ℕ) : ∀ i : Fin 23, i = 15 ∨ i = 16 →
    66 ≤ (stageBank (pivotSlots.trans entrySlots) r i).val := by
  induction r with
  | zero => intro i h; rcases h with rfl | rfl <;> decide
  | succ r ih =>
    intro i h
    apply ih (Equiv.swap 15 16 i)
    rcases h with rfl | rfl <;> simp

/-- Read the current directory label and put its actual conjugate on the
parity-selected archive input. All other tapes return to their entry state. -/
theorem ordinaryMatrix_exec {m w W H J Q common work : ℕ} {P U : Type}
    (v : RecursiveInterchangeLayout.Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (weights : Fin m → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (schedules : List ℕ → List (Fin (prime+4)))
    (hm : prime^(w+1) < 2^H) (poolFits : (RingFormula.conjugationDepth m+1)*13 ≤ work)
    (room : 58 ≤ common+24+31+work) (r : ℕ) :
    let K := common+24+31+work
    let src := directoryRecordMatrixSlot common work
    let full := ordinaryCaller room
    let dst := stageBank (pivotSlots.trans full) r 15
    let tmp : Fin (66+K) := (59 : Fin 66).castAdd K
    ∀ (body : P → Pr P (66+K) Q prime U) u S j js,
      DirectoryReady v proj w W H J weights prefixes tail schedules S (j::js) →
      LabelStock.live m (w+1) 1 j = true →
      let g := physicalLabel m (w+1) j
      let G := g*IntegerMultBounds.Swap.Modular.reduce (prime^(w+1)) proj*g⁻¹
      ∃ z n, z.user = u.user ∧ n ≤ (RingFormula.conjugationDepth m+1)*(6*H+6)+1 +
        ((4*H+4)+(recordConjugationTime m w H (prefixes j).length+(2*H+2))+
        ((RingFormula.conjugationDepth m+1)*(2*H+2)+1)) + (4*(m*m*H)+4) ∧
        Exec body ((directoryRecordWriter m common poolFits).seq
          (if src = dst then .act .done else moveRightOrdered src tmp dst)) (mk u S) n
          (mk z {S with R := Function.update S.R dst (matrixWords prime H G)}) := by
  intro K src full dst tmp body u S j js ready live g G
  obtain ⟨y,n,user,bill,write⟩ := generatedRecordMatrix_exec (common := common) v proj weights prefixes tail schedules
    hm poolFits body u S j js ready live
  have srcVal : src.val = 66+(common+16) := rfl
  have slotVal (i : Fin 23) : (stageBank (pivotSlots.trans full) r i).val =
      (stageBank (pivotSlots.trans entrySlots) r i).val := by rw [stageBank_swap,stageBank_swap]; rfl
  have dstVal : 66 ≤ dst.val := (slotVal 15).symm ▸ archiveSlots_private r 15 (Or.inl rfl)
  have free := ready.2.2.1
  have hs := (free src (by omega)).2
  have hd := (free dst (by omega)).2
  have ht := (free tmp (by change 58 ≤ 59; decide)).2
  change Exec body _ _ _ (mk y {S with R := Function.update S.R src (matrixWords prime H G ++ S.R src)}) at write
  rw [hs,List.append_nil] at write
  have small : tmp.val = 59 := rfl
  obtain ⟨z,t,same,charge,transfer⟩ := forwardWritten_exec body src dst tmp
    (fun eq => by have := congrArg Fin.val eq; omega) (fun eq => by have := congrArg Fin.val eq; omega)
    (matrixWords prime H G) y S hs hd ht
  rw [length_matrixWords] at charge
  exact ⟨z,n+t,same.trans user,Nat.add_le_add bill charge,Exec.seq write transfer⟩

/-- Generate the live record's matrix and retain its elimination archive and pivots.
Readiness of the directory supplies every scratch-tape and header premise. -/
theorem ordinaryGeneratedArchive_exec {m w W H J Q common work : ℕ} {P U : Type}
    (v : RecursiveInterchangeLayout.Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (weights : Fin m → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (schedules : List ℕ → List (Fin (prime+4)))
    (hm : prime^(w+1) < 2^H) (poolFits : (RingFormula.conjugationDepth m+1)*13 ≤ work)
    (room : 58 ≤ common+24+31+work) :
    let K := common+24+31+work
    let src := directoryRecordMatrixSlot common work
    let full := ordinaryCaller room
    let r := proj.rank
    let slots := stageBank (pivotSlots.trans full) r
    let tmp := (59 : Fin 66).castAdd K
    let program : Pr P (66+K) Q prime U :=
      ((directoryRecordWriter m common poolFits).seq (if src = slots 15 then .act .done
        else moveRightOrdered src tmp (slots 15))).seq (goodWeights prime r proj.rank_le_height slots : Pr P (66+K) Q prime U)
    ∀ (body : P → Pr P (66+K) Q prime U) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime) (j : ℕ) (js : List ℕ), DirectoryReady v proj w W H J weights prefixes tail schedules S (j::js) →
      LabelStock.live m (w+1) 1 j = true →
      let g := physicalLabel m (w+1) j
      let M := IntegerMultBounds.Swap.Modular.reduce (prime^(w+1)) proj
      let G := g*M*g⁻¹
      fallbackBit proj.rank_le_height M g = false →
      ∃ minor : ∀ k (hk : k < r), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk proj.rank_le_height) G).det,
      let words := fun k => if hk : k ≤ r then matrixWords prime H (GoodForm.stageAt G r proj.rank_le_height minor k hk).M else []
      let stage := GoodForm.stageAt G r proj.rank_le_height minor r le_rfl
      ∃ z D n, z.user = u.user ∧ Exec body program (mk u S) n (mk z D) ∧
        n ≤ (RingFormula.conjugationDepth m+1)*(6*H+6)+1 +
          ((4*H+4)+(recordConjugationTime m w H (prefixes j).length+(2*H+2))+((RingFormula.conjugationDepth m+1)*(2*H+2)+1)) +
          (4*(m*m*H)+4) + (r*(4*w+4+columnTime m prime w H)+1+(r*(8*(m*m*H)+14*H+22)+1)) ∧
        D.R (full 47) = (List.ofFn fun i : Fin r => binSyms H (stage.M (i.castLE proj.rank_le_height) (i.castLE proj.rank_le_height)).val).flatten ∧
        (D.R (full 49),D.R (full 50)) = matrixArchive words (words 0) [] r ∧ D.L = S.L ∧
        ∀ i, i ≠ full 47 → i ≠ full 49 → i ≠ full 50 → D.R i = S.R i := by
  intro K src full r slots tmp program body u S j js ready live g M G clear
  have unit := (physicalLabel_live (m := m) (by omega : 0 < w+1) j).mp live
  have minor (k) (hk : k < r) : IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk proj.rank_le_height) G).det := by
    by_contra missing
    have bad : fallbackBit proj.rank_le_height M g = true := decide_eq_true ⟨unit,k,hk,missing⟩
    exact Bool.noConfusion (bad.symm.trans clear)
  refine ⟨minor,?_⟩
  intro words stage
  obtain ⟨y,n,user,price,write⟩ := ordinaryMatrix_exec v proj weights prefixes tail schedules hm poolFits room r
    body u S j js ready live
  let B := {S with R := Function.update S.R (slots 15) (matrixWords prime H G)}
  have keep (i : Fin 23) (off : i ≠ 15) : B.R (slots i) = S.R (slots i) :=
    Function.update_of_ne (slots.injective.ne off) ..
  have fixed (i : Fin 23) (h : i ≠ 15) (k : i ≠ 16) : slots i = full (pivotSlots i) :=
    stageBank_fixed _ _ _ h k
  have scratch (i : Fin 23) (hi : (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21) : B.R (slots i) = [] := by
    rw [keep i (by omega),fixed i (by omega) (by omega)]
    exact (ready.2.2.1 _ ((by decide : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 →
      58 ≤ (entrySlot (pivotSlots i)).val) i hi)).2
  have other : B.R (slots 16) = [] := by
    rw [keep _ (by decide)]
    apply (ready.2.2.1 _ _).2
    change 58 ≤ (stageBank (pivotSlots.trans full) r 16).val
    rw [stageBank_swap]
    have bound := archiveSlots_private r 16 (Or.inr rfl)
    rw [stageBank_swap] at bound
    exact (by decide : 58 ≤ 66).trans bound
  obtain ⟨z,D,t,same,bill,archive,piv,pair,left,frame⟩ := ordinaryArchive_exec room body G r proj.rank_le_height minor hm y B
    (by rw [keep _ (by decide),fixed _ (by decide) (by decide)]; exact ready.2.2.2.2.2.1)
    (by rw [keep _ (by decide),fixed _ (by decide) (by decide)]; exact ready.2.2.2.2.2.2.2.2.2.1)
    (by rw [keep _ (by decide),fixed _ (by decide) (by decide)]; exact ready.2.2.2.2.2.2.2.2.2.2.1)
    scratch [] (by rw [List.append_nil]; exact Function.update_self (slots 15) _ S.R)
  refine ⟨z,D,n+t,same.trans user,Exec.seq write archive,Nat.add_le_add price bill,piv,?_,left,?_⟩
  · rw [other] at pair
    have first : B.R (slots 15) = words 0 := by
      change (Function.update S.R (slots 15) (matrixWords prime H G)) (slots 15) = _
      rw [Function.update_self]
      simp only [words,dite_eq_left (Nat.zero_le r),GoodForm.stageAt]
      rfl
    exact pair.trans (congrArg (fun source => matrixArchive words source [] r) first)
  · intro i hp ha hb
    rw [frame i hp ha hb]
    apply Function.update_of_ne
    have either (n) : ∀ k : Fin 23, k = 15 ∨ k = 16 →
        stageBank (pivotSlots.trans full) n k = full 49 ∨ stageBank (pivotSlots.trans full) n k = full 50 := by
      induction n with
      | zero => intro k h; rcases h with rfl | rfl; exact Or.inl rfl; exact Or.inr rfl
      | succ n ih => intro k h; apply ih (Equiv.swap 15 16 k); rcases h with rfl | rfl <;> simp
    exact fun eq => (either r 15 (Or.inl rfl)).elim (fun h => ha (eq.trans h)) (fun h => hb (eq.trans h))

end IntegerMultBounds.MathlibTM2.M6.BitNode
