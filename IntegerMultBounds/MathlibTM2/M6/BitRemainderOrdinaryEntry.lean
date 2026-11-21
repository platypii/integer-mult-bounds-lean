module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinary
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderReciprocal
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
    (u : HS (66+K) Q prime U) (initial S : Stacks (66+K) prime)
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedules initial pending)
    (left : S.L = initial.L)
    (frame : ∀ i, i ≠ ordinaryCaller room 47 → i ≠ ordinaryCaller room 49 →
      i ≠ ordinaryCaller room 50 → i ≠ ordinaryCaller room 51 → i ≠ ordinaryCaller room 54 → S.R i = initial.R i)
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
  have same (i : Fin 58) (off : i ∉ ([47,49,50,51,54] : List (Fin 58))) : S.R (full i) = initial.R (full i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at off
    exact frame _ (full.injective.ne off.1) (full.injective.ne off.2.1) (full.injective.ne off.2.2.1) (full.injective.ne off.2.2.2.1) (full.injective.ne off.2.2.2.2)
  have privatePort (i : Fin 58) (hi : 58 ≤ (entrySlot i).val) (off : i ∉ ([47,49,50,51,54] : List (Fin 58))) :
      S.L (full i) = [] ∧ S.R (full i) = [] := by rw [left,same i off]; exact privateBlank _ hi
  have baseSlot : S.R (full 2) = binSyms H M := (same 2 (by decide)).trans base
  obtain ⟨z,user,run⟩ := bcopy_exec (body := body)
    ((by decide : ([2,33,0,1] : List (Fin 58)).Nodup).map full.injective)
    u S (privatePort 0 (by decide) (by decide)).2 (privatePort 1 (by decide) (by decide)).2
  simp only [baseSlot,(privatePort 33 (by decide) (by decide)).2,List.append_nil,length_binSyms] at run
  let D := {S with R := Function.update S.R (full 33) (binSyms H M)}
  have keep (i : Fin 58) (hi : i ≠ 33) : D.R (full i) = S.R (full i) :=
    Function.update_of_ne (full.injective.ne hi) ..
  have free (i : Fin 58) (hi : 58 ≤ (entrySlot i).val) (off : i ≠ 33) (archive : i ∉ ([47,49,50,51,54] : List (Fin 58))) :
      D.L (full i) = [] ∧ D.R (full i) = [] := ⟨(privatePort i hi archive).1,(keep _ off).trans (privatePort i hi archive).2⟩
  refine ⟨z,D,user,run,?_,rfl⟩
  constructor
  · exact (free 52 (by decide) (by decide) (by decide)).2
  · exact (keep 48 (by decide)).trans ((same 48 (by decide)).trans parentStored)
  · exact (free 41 (by decide) (by decide) (by decide)).2
  · exact Function.update_self (full 33) (binSyms H M) S.R
  · intro j hj
    let i := (coeff true j).castLE (by decide : 53 ≤ 58)
    have bounds := (by decide : ∀ j : Fin 17, j ≤ 1 ∨ 3 ≤ j ∧ j ≤ 11 →
      58 ≤ (entrySlot ((coeff true j).castLE (by decide))).val ∧ (coeff true j).val ≠ 33 ∧ (coeff true j).castLE (by decide) ∉ ([47,49,50,51,54] : List (Fin 58))) j hj
    exact (free i bounds.1 (fun eq => bounds.2.1 (congrArg Fin.val eq)) bounds.2.2).2
  · exact (keep 2 (by decide)).trans ((same 2 (by decide)).trans base)
  · exact (keep 28 (by decide)).trans ((same 28 (by decide)).trans one)
  · exact (keep 53 (by decide)).trans ((same 53 (by decide)).trans width)
  · intro j hj
    let i := (entry j).castLE (by decide : 54 ≤ 58)
    have bounds := (by decide : ∀ j ∈ headShearWork,
      58 ≤ (entrySlot ((entry j).castLE (by decide))).val ∧ (entry j).val ≠ 33 ∧ (entry j).castLE (by decide) ∉ ([47,49,50,51,54] : List (Fin 58))) j hj
    exact free i bounds.1 (fun eq => bounds.2.1 (congrArg Fin.val eq)) bounds.2.2
  · intro k
    simpa only [sub_zero,show ports 24 = full 24 from rfl,keep 24 (by decide)] using payload k
  · intro k
    obtain ⟨l,r⟩ := free 25 (by decide) (by decide) (by decide)
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

/-- The modulus word clocks the full matrix archive, including for inherited weights.
Only the archive-length tape changes, so this can follow pivot generation. -/
theorem ordinaryArchiveLength_exec {T Q m H : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (full : Fin 58 ↪ Fin T)
    (u : HS T Q prime U) (S : Stacks T prime)
    (width : (S.R (full 2)).length = H) (empty : S.R (full 51) = [])
    (scratch : S.R (full 0) = []) :
    ∃ z, z.user = u.user ∧
      Exec body (Node.umul (m*m) (full 2) (full 51) (full 0)) (mk u S) (4*H+4)
        (mk z {S with R := Function.update S.R (full 51) (List.replicate (m*m*H) Node.tick)}) := by
  obtain ⟨z,user,run⟩ := Node.umulSym_exec body (m*m) Node.tick (a := full 2) (b := full 51)
    (t := full 0) (full.injective.ne (by decide)) (full.injective.ne (by decide))
    (full.injective.ne (by decide)) u S scratch
  exact ⟨z,user,by simpa only [Node.umul,width,empty,List.append_nil] using run⟩

/-- The inherited diagonal, modulus, one and precision clock are shared with the
directory. All other reciprocal-reader registers are private scratch. -/
def ordinaryReciprocalPorts : Fin 19 ↪ Fin 58 :=
  ⟨![0,1,3,4,2,5,6,7,8,9,10,11,12,13,14,44,45,17,48],by decide⟩

theorem ordinaryReciprocals_exec {T Q m w H : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (full : Fin 58 ↪ Fin T)
    (weight : Fin m → ZMod (prime^(w+1))) (unit : ∀ i, IsUnit (weight i))
    (hm : prime^(w+1) < 2^H) (v : HS T Q prime U) (S : Stacks T prime)
    (weights : S.R (full 48) = (List.ofFn fun j => binSyms H (weight j).val).flatten)
    (modulus : S.R (full 2) = binSyms H (prime^(w+1)))
    (one : S.R (full 44) = binSyms H (1 : ZMod (prime^(w+1))).val)
    (clock : (S.R (full 45)).length = w)
    (free : ∀ j : Fin 58, j ≤ 17 → j ≠ 2 → S.R (full j) = []) :
    let word := fun i => binSyms (A := prime) H (Ring.inverse (weight i)).val
    let C := 48*H*H+152*H+66
    let cost := fun i : Fin m => (8*(i.val*H)+14*H+22) +
      (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) + (2*H+2) + (4*H+4)
    ∃ z t, z.user = v.user ∧ t ≤ ((List.finRange m).map cost).sum+1 ∧
      Exec body (packReciprocals prime (ordinaryReciprocalPorts.trans full) (full 54) (List.finRange m))
        (mk v S) t (mk z {S with R := Function.update S.R (full 54) ((List.ofFn word).flatten ++ S.R (full 54))}) := by
  intro word C cost
  letI : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩
  have apart : ∀ j, ordinaryReciprocalPorts j ≠ 54 := by decide
  have scratch : ∀ j : Fin 19, (j < 13 ∧ j ≠ 4) ∨ j = 14 ∨ j = 17 →
      ordinaryReciprocalPorts j ≤ 17 ∧ ordinaryReciprocalPorts j ≠ 2 := by decide
  simpa only [List.flatMap_def,List.ofFn_eq_map] using
    packReciprocals_exec body (ordinaryReciprocalPorts.trans full) (full 54)
      (fun j => full.injective.ne (apart j)) weight (List.finRange m) unit prime_prime H hm v S []
      (weights.trans (List.append_nil _).symm) modulus one clock
      (fun j hj => free _ (scratch j hj).1 (scratch j hj).2)

theorem ordinarySetup_exec {K m w W H J Q : ℕ} {P U : Type} (room : 58 ≤ K)
    (body : P → Pr P (66+K) Q prime U) (v : RecursiveInterchangeLayout.Descriptor)
    (proj : Matrix (Fin m) (Fin m) ℚ) (weights : Fin m → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (schedules : List ℕ → List (Fin (prime+4))) (pending : List ℕ)
    (u : HS (66+K) Q prime U) (initial S : Stacks (66+K) prime)
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedules initial pending)
    (left : S.L = initial.L)
    (frame : ∀ i, i ≠ ordinaryCaller room 47 → i ≠ ordinaryCaller room 49 →
      i ≠ ordinaryCaller room 50 → S.R i = initial.R i)
    (unit : ∀ i, IsUnit (weights i)) (hm : prime^(w+1) < 2^H)
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
    let invWords := (List.ofFn fun i => binSyms (A := prime) H (Ring.inverse (weights i)).val).flatten
    let C := 48*H*H+152*H+66
    let cost := fun i : Fin m => (8*(i.val*H)+14*H+22) +
      (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) + (2*H+2) + (4*H+4)
    let load := packReciprocals prime (ordinaryReciprocalPorts.trans full) (full 54) (List.finRange m)
    let childBank := child.trans (head.trans bank)
    ∃ z D t, z.user = u.user ∧ t ≤ ((List.finRange m).map cost).sum+1+(4*H+4)+(6*H+6) ∧
      Exec body (load.seq ((Node.umul (m*m) (full 2) (full 51) (full 0)).seq
        (bcopy (full 2) (full 33) (full 0) (full 1)))) (mk u S) t (mk z D) ∧
      HeadColumnReady (d := m+m) (W := W) coeffs ports H J [] parentWords [] SparseRoleCircuit.encode
        (fun _ => blank) (fun _ => blank) 0 0 word D ∧
      D.R (bank 27) = [] ∧
      D.R (childBank 15) = binSyms H (1 : ZMod M).val ∧ (D.R (childBank 16)).length = w ∧
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → D.R (childBank j) = []) ∧
      (∀ i ∈ [full 55,full 56,full 57], D.R i = []) ∧
      (∀ i, 66+58 ≤ i.val → D.L i = [] ∧ D.R i = []) ∧
      D = {S with R := Function.update (Function.update (Function.update S.R (full 54) invWords)
        (full 51) (List.replicate (m*m*H) Node.tick)) (full 33) (binSyms H M)} := by
  intro M full bank coeffs ports parentWords payload invWords C cost load childBank
  obtain ⟨_,_,privateBlank,_,_,base,_,_,_,one,clock,stored,_⟩ := (show DirectoryReady _ _ _ _ _ _ _ _ _ _ _ _ from ready)
  have keep (i : Fin 58) (h : i ∉ ([47,49,50] : List (Fin 58))) : S.R (full i) = initial.R (full i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact frame _ (full.injective.ne h.1) (full.injective.ne h.2.1) (full.injective.ne h.2.2)
  have free (i : Fin 58) (hi : 58 ≤ (entrySlot i).val) (h : i ∉ ([47,49,50] : List (Fin 58))) :
      S.R (full i) = [] := (keep i h).trans (privateBlank _ hi).2
  have scratch := (by decide : ∀ j : Fin 58, j ≤ 17 → j ≠ 2 →
    58 ≤ (entrySlot j).val ∧ j ∉ ([47,49,50] : List (Fin 58)))
  obtain ⟨y,n,hy,hn,rinv⟩ := ordinaryReciprocals_exec body full weights unit hm u S
    ((keep 48 (by decide)).trans stored) ((keep 2 (by decide)).trans base) ((keep 44 (by decide)).trans one)
    ((congrArg List.length (keep 45 (by decide))).trans clock) (fun j hj h => free j (scratch j hj h).1 (scratch j hj h).2)
  rw [free 54 (by decide) (by decide),List.append_nil] at rinv
  let B := {S with R := Function.update S.R (full 54) invWords}
  have same (i : Fin 58) (hi : i ≠ 54) : B.R (full i) = S.R (full i) := Function.update_of_ne (full.injective.ne hi) ..
  obtain ⟨x,hx,len⟩ := ordinaryArchiveLength_exec (m := m) body full y B
    ((congrArg List.length ((same 2 (by decide)).trans ((keep 2 (by decide)).trans base))).trans (length_binSyms ..))
    ((same 51 (by decide)).trans (free 51 (by decide) (by decide))) ((same 0 (by decide)).trans (free 0 (by decide) (by decide)))
  let E := {B with R := Function.update B.R (full 51) (List.replicate (m*m*H) Node.tick)}
  have unchanged (i) (h : i ≠ full 51) (k : i ≠ full 54) : E.R i = S.R i :=
    (Function.update_of_ne h ..).trans (Function.update_of_ne k ..)
  obtain ⟨z,D,hz,entryRun,headReady,result⟩ := ordinaryEntry_exec room body v proj weights prefixes tail schedules pending
    x initial E ready left (fun i a b c h k => (unchanged i h k).trans (frame i a b c)) word
    (by intro k; change _ = readAt blank (S.L (full 24)) (E.R (full 24)) k; rw [unchanged _ (full.injective.ne (by decide)) (full.injective.ne (by decide))]; exact payload k)
  have fixed (i : Fin 58) (off : i ∉ ([33,51,54] : List (Fin 58))) : D.R (full i) = S.R (full i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at off
    rw [result]
    exact (Function.update_of_ne (full.injective.ne off.1) ..).trans
      (unchanged _ (full.injective.ne off.2.1) (full.injective.ne off.2.2))
  have blankPort (i : Fin 58) (hi : 58 ≤ (entrySlot i).val)
      (old : i ∉ ([47,49,50] : List (Fin 58))) (newPort : i ∉ ([33,51,54] : List (Fin 58))) :
      D.R (full i) = [] := (fixed i newPort).trans (free i hi old)
  refine ⟨z,D,_,hz.trans (hx.trans hy),by dsimp [cost,C] at *; omega,
    Exec.seq rinv (Exec.seq len entryRun),headReady,blankPort 27 (by decide) (by decide) (by decide),
    (fixed 44 (by decide)).trans ((keep 44 (by decide)).trans one),
    (congrArg List.length ((fixed 45 (by decide)).trans (keep 45 (by decide)))).trans clock,?_,?_,?_,result⟩
  · intro j hj
    let i : Fin 58 := (child j).castLE (by decide)
    have bounds := (by decide : ∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 →
      let i : Fin 58 := (child j).castLE (by decide)
      58 ≤ (entrySlot i).val ∧ i ∉ ([47,49,50] : List (Fin 58)) ∧ i ∉ ([33,51,54] : List (Fin 58))) j hj
    exact blankPort i bounds.1 bounds.2.1 bounds.2.2
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact blankPort _ (by decide) (by decide) (by decide)
  · intro i hi
    have apart (j : Fin 58) : i ≠ full j := by
      intro eq
      have bound := (entrySlot j).isLt
      change i.val ≥ 66+58 at hi
      rw [eq] at hi
      change 66+58 ≤ (entrySlot j).val at hi
      omega
    have blank := privateBlank i (by omega)
    rw [result]
    exact ⟨(congrFun left i).trans blank.1,(Function.update_of_ne (apart 33) ..).trans
      ((unchanged i (apart 51) (apart 54)).trans ((frame i (apart 47) (apart 49) (apart 50)).trans blank.2))⟩

noncomputable def ordinarySetupTime (m r w H prefixLength : ℕ) : ℕ :=
    let C : ℕ := 48*H*H+152*H+66
    let cost := fun i : Fin m => (8*(i.val*H)+14*H+22) +
      (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) + (2*H+2) + (4*H+4)
    ((RingFormula.conjugationDepth m+1)*(6*H+6)+1 +
          ((4*H+4)+(recordConjugationTime m w H prefixLength+(2*H+2))+((RingFormula.conjugationDepth m+1)*(2*H+2)+1)) +
          (4*(m*m*H)+4) + (r*(4*w+4+columnTime m prime w H)+1+(r*(8*(m*m*H)+14*H+22)+1))) + (((List.finRange m).map cost).sum+1+(4*H+4)+(6*H+6))

theorem ordinaryGeneratedSetup_exec {m w W H J Q common work : ℕ} {P U : Type}
    (v : RecursiveInterchangeLayout.Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (weights : Fin m → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (schedules : List ℕ → List (Fin (prime+4)))
    (hm : prime^(w+1) < 2^H) (poolFits : (RingFormula.conjugationDepth m+1)*13 ≤ work)
    (unit : ∀ i, IsUnit (weights i))
    (room : 58 ≤ common+24+31+work)
    (body : P → Pr P (66+(common+24+31+work)) Q prime U) (u : HS (66+(common+24+31+work)) Q prime U) (S : Stacks (66+(common+24+31+work)) prime) (j : ℕ) (js : List ℕ)
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedules S (j::js))
    (live : LabelStock.live m (w+1) 1 j = true) :
    letI : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩
    let K := common+24+31+work
    let src := directoryRecordMatrixSlot common work
    let full := ordinaryCaller room
    let r := proj.rank
    let slots := stageBank (pivotSlots.trans full) r
    let tmp := (59 : Fin 66).castAdd K
    let program : Pr P (66+K) Q prime U :=
      ((directoryRecordWriter m common poolFits).seq (if src = slots 15 then .act .done
        else moveRightOrdered src tmp (slots 15))).seq (goodWeights prime r proj.rank_le_height slots : Pr P (66+K) Q prime U)
      let g := physicalLabel m (w+1) j
      let M := IntegerMultBounds.Swap.Modular.reduce (prime^(w+1)) proj
      let G := g*M*g⁻¹
      fallbackBit proj.rank_le_height M g = false →
      ∀ word : Fin ((prime^(w+1))^(m+m)*W) → ZMod 2,
    (∀ z, RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
      (List.ofFn (SparseRoleCircuit.encode ∘ word)) z) = readAt blank (S.L (full 24)) (S.R (full 24)) z) →
      ∃ minor : ∀ (k : ℕ) (hk : k < r), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk proj.rank_le_height) G).det,
      let words := fun k => if hk : k ≤ r then matrixWords prime H (GoodForm.stageAt G r proj.rank_le_height minor k hk).M else []
      let stage := GoodForm.stageAt G r proj.rank_le_height minor r le_rfl
    let bank := adapterBank.trans (parent.trans (parentWithWeights.trans full))
    let coeffs := (coeff true).trans (head.trans bank)
    let ports := entry.trans bank
    let parentWords := (List.ofFn fun i => binSyms (A := prime) H (weights i).val).flatten
    let invWords := (List.ofFn fun i => binSyms (A := prime) H (Ring.inverse (weights i)).val).flatten
    let load : Pr P (66+K) Q prime U := packReciprocals prime (ordinaryReciprocalPorts.trans full) (full 54) (List.finRange m)
    let childBank := child.trans (head.trans bank)
    ∃ (z : HS (66+K) Q prime U) (D : Stacks (66+K) prime) (t : ℕ), z.user = u.user ∧ t ≤ ordinarySetupTime m r w H (prefixes j).length ∧
      Exec body (program.seq (load.seq ((Node.umul (m*m) (full 2) (full 51) (full 0)).seq
        (bcopy (full 2) (full 33) (full 0) (full 1))))) (mk u S) t (mk z D) ∧
      HeadColumnReady (d := m+m) (W := W) coeffs ports H J [] parentWords [] SparseRoleCircuit.encode
        (fun _ => blank) (fun _ => blank) 0 0 word D ∧
      D.R (bank 27) = [] ∧
      D.R (childBank 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ (D.R (childBank 16)).length = w ∧
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → D.R (childBank j) = []) ∧
      (∀ i ∈ [full 55,full 56,full 57], D.R i = []) ∧
      (∀ i, 66+58 ≤ i.val → D.L i = [] ∧ D.R i = []) ∧
      D.R (full 54) = invWords ∧ (D.R (full 51)).length = m*m*H ∧
      D.R (full 47) = (List.ofFn fun i : Fin r => binSyms H (stage.M (i.castLE proj.rank_le_height) (i.castLE proj.rank_le_height)).val).flatten ∧
      (D.R (full 49),D.R (full 50)) = matrixArchive words (words 0) [] r ∧
      (∀ i, i.val < 66 → D.R i = S.R i) := by
  intro K src full r slots tmp program g M G clear word payload
  obtain ⟨minor,generated⟩ :=
    ordinaryGeneratedArchive_exec v proj weights prefixes tail schedules hm poolFits room body u S j js ready live clear
  refine ⟨minor,?_⟩
  intro words stage bank coeffs ports parentWords invWords load childBank
  obtain ⟨y,B,n,hy,archive,hn,pivots,pair,left,frame⟩ := generated
  have payloadB : B.R (full 24) = S.R (full 24) := frame _ (full.injective.ne (by decide))
    (full.injective.ne (by decide)) (full.injective.ne (by decide))
  obtain ⟨z,D,t,hz,ht,setup,headReady,empty,one,clock,free,temps,extra,result⟩ :=
    ordinarySetup_exec room body v proj weights prefixes tail schedules (j::js) y S B ready left frame unit hm word
      (by intro k; change _ = readAt blank (B.L (full 24)) (B.R (full 24)) k; rw [left,payloadB]; exact payload k)
  refine ⟨z,D,_,hz.trans hy,Nat.add_le_add hn ht,Exec.seq archive setup,headReady,empty,one,clock,free,temps,extra,?_,?_,?_,?_,?_⟩
  all_goals rw [result]
  case refine_5 =>
    intro i hi
    have apart (k : Fin 58) (hk : 66 ≤ (entrySlot k).val) : i ≠ full k := by
      intro eq
      rw [eq] at hi
      change (entrySlot k).val < 66 at hi
      omega
    exact (Function.update_of_ne (apart 33 (by decide)) ..).trans
      ((Function.update_of_ne (apart 51 (by decide)) ..).trans
        ((Function.update_of_ne (apart 54 (by decide)) ..).trans
          (frame _ (apart 47 (by decide)) (apart 49 (by decide)) (apart 50 (by decide)))))
  all_goals simp only [full,Function.update_apply,(ordinaryCaller room).injective.eq_iff,invWords] <;> norm_num <;> assumption

open GoodForm FlatCoordinateLayout LabelTraversal Matrix M8.Exchange M8.ReversedExchange
open IntegerMultBounds.Swap.Shear

def OrdinaryRecordExec [M8.Machine.Net] {N Q m w W H J rank : ℕ} {P U : Type}
    (cap : 217 ≤ Q) (hr : rank ≤ m) (full : Fin 58 ↪ Fin N)
    (body : P → Pr P N Q prime U) (overhead budget : ℕ)
    (G : Matrix (Fin m) (Fin m) (ZMod (prime^(w+1))))
    (minor : ∀ k (hk : k < rank), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (weights : Fin m → ZMod (prime^(w+1))) (proc : P := by exact ())
    (context : Stacks N prime → Prop := fun _ => True) : Prop :=
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩
    let bank := adapterBank.trans (parent.trans (parentWithWeights.trans full))
    let host := head.trans bank
    let c := child.trans host
    let parentWords := (List.ofFn fun i => binSyms (A := prime) H (weights i).val).flatten
    let ready := HeadColumnReady (d := m+m) (W := W) ((coeff true).trans host) (entry.trans bank)
      H J [] parentWords [] SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let words := fun k => if hk : k ≤ rank then matrixWords prime H (stageAt G rank hr minor k hk).M else []
    let stage := stageAt G rank hr minor rank le_rfl
    ∀ v S word, context S → ready word S → S.R (bank 27) = [] →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      (∀ i ∈ [full 55,full 56,full 57], S.R i = []) →
      (∀ i, 124 ≤ i.val → S.L i = [] ∧ S.R i = []) →
      S.R (full 54) = (List.ofFn fun i => binSyms H (Ring.inverse (weights i)).val).flatten →
      (S.R (full 51)).length = m*m*H →
      S.R (full 47) = (List.ofFn fun i : Fin rank => binSyms H (stage.M (i.castLE hr) (i.castLE hr)).val).flatten →
      (S.R (full 49),S.R (full 50)) = matrixArchive words (words 0) [] rank →
      ∃ z F t out, z.user = v.user ∧ t ≤ budget + overhead*(M^(m+m)*W) ∧
        Exec body (hostedGoodRecordAt cap full full proc prime rank (m-rank) hr) (mk v S) t (mk z F) ∧
        ready out F ∧ F.R (bank 27) = [] ∧
        (∀ j, (∀ i, (shear.trans host) i ≠ j) → (∀ i, (shear.trans (ordinaryHead.trans bank)) i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j) ∧
        (∀ j, j ≠ full 24 →
          let growth := goodRecordStackGrowth (U := U) (A := prime) (GoodChildLayout.parent.trans (parentWithWeights.trans full)) prime w W H J rank hr
          (F.L j).length ≤ (S.L j).length+growth ∧ (F.R j).length ≤ (S.R j).length+growth) ∧
        ∀ x j, let y := transform (diagonal weights) 1 (revExchangeOf (rev m) G
                (transform (diagonal fun i => Ring.inverse (weights i)) 1 x))
               out (index (Fin.append y.1 y.2) j) = word (index (Fin.append x.1 x.2) j)

/-- Run the stopped adapter on the archive emitted by ordinary record preparation.
The shared middle header describes a single block, so it needs no extra tape. -/
theorem ordinaryPreparedRun_exec [M8.Machine.Net] {n T Q d w W H J rank : ℕ} {U : Type}
    (cap : 217 ≤ Q) (hr : rank ≤ d+1) (caller : Fin 58 ↪ Fin n)
    (body : Unit → Pr Unit (n+T) Q prime U) (C : ℝ) (overhead budget : ℕ)
    (G : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod (prime^(w+1))))
    (minor : ∀ k (hk : k < rank), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (weights : Fin (d+1) → ZMod (prime^(w+1))) (enough : 124 ≤ n)
    (width : H = Nat.size (prime^(w+1))) (digits : J = Nat.size W)
    (run : Record.StoppedRecordRun (g := d+1-rank) (digits := 0) (W := W) (H := H) (J := J)
      cap hr caller caller body C overhead budget ⟨1,1,1,d+1,1,W⟩ G minor weights
      (fun i => Ring.inverse (weights i)) [] [] [] [] [] (fun _ => blank) 0) :
    OrdinaryRecordExec (W := W) (H := H) (J := J) cap hr (caller.trans (Fin.castAddEmb T))
      body overhead budget G minor weights := by
  unfold OrdinaryRecordExec
  let full := caller.trans (Fin.castAddEmb T)
  intro M bank host c parentWords ready words stage v S word _ headReady empty one clock free temps extra inverses length pivots pair
  obtain ⟨z,F,t,out,user,_,price,exec,restored,blankPort,frame,growth,correct⟩ := run v S word
    (by simpa only [List.append_nil] using headReady) empty (by rw [List.append_nil]; exact inverses)
    (by rw [List.append_nil]; exact pair) length (by rw [List.append_nil]; exact pivots)
    one clock free temps (Or.inl ⟨rfl,by simp⟩) (fun i hi => extra i (enough.trans hi))
  exact ⟨z,F,t,out,user,(price width digits).1,exec,by simpa only [List.append_nil] using restored,
    blankPort,frame,growth,correct⟩


open IntegerMultBounds.MathlibTM2.Fast.Main in
theorem ordinaryGeneratedRecord_exec [M8.Machine.Net] {d w W H J Q common work : ℕ} {P U : Type}
    (cap : 217 ≤ Q) (overhead budget : ℕ)
    (v : RecursiveInterchangeLayout.Descriptor) (proj : Matrix (Fin (d+1)) (Fin (d+1)) ℚ)
    (weights : Fin (d+1) → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (schedules : List ℕ → List (Fin (prime+4)))
    (hm : prime^(w+1) < 2^H) (poolFits : (RingFormula.conjugationDepth (d+1)+1)*13 ≤ work)
    (unit : ∀ i, IsUnit (weights i))
    (room : 58 ≤ common+24+31+work)
    (body : P → Pr P (66+(common+24+31+work)) Q prime U) (u : HS (66+(common+24+31+work)) Q prime U) (S : Stacks (66+(common+24+31+work)) prime) (j : ℕ) (js : List ℕ)
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedules S (j::js))
    (live : LabelStock.live (d+1) (w+1) 1 j = true)
    (proc : P := by exact ())
    (context : Stacks (66+(common+24+31+work)) prime → Prop := fun _ => True)
    (preserved : ∀ D, (∀ i, i.val < 58 → D.R i = S.R i) → context D := by intros; trivial) :
    letI : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩
    let m := d+1
    let K := common+24+31+work
    let src := directoryRecordMatrixSlot common work
    let full := ordinaryCaller room
    let r := proj.rank
    let slots := stageBank (pivotSlots.trans full) r
    let tmp := (59 : Fin 66).castAdd K
    let program : Pr P (66+K) Q prime U :=
      ((directoryRecordWriter m common poolFits).seq (if src = slots 15 then .act .done
        else moveRightOrdered src tmp (slots 15))).seq (goodWeights prime r proj.rank_le_height slots : Pr P (66+K) Q prime U)
      let g := physicalLabel m (w+1) j
      let M := IntegerMultBounds.Swap.Modular.reduce (prime^(w+1)) proj
      let G := g*M*g⁻¹
      fallbackBit proj.rank_le_height M g = false →
      ∀ word : Fin ((prime^(w+1))^(m+m)*W) → ZMod 2,
    (∀ z, RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
      (List.ofFn (SparseRoleCircuit.encode ∘ word)) z) = readAt blank (S.L (full 24)) (S.R (full 24)) z) →
    (∀ minor, OrdinaryRecordExec (W := W) (H := H) (J := J) cap proj.rank_le_height full body overhead budget G minor weights proc context) →
    let load : Pr P (66+K) Q prime U := packReciprocals prime (ordinaryReciprocalPorts.trans full) (full 54) (List.finRange m)
    let prepare := program.seq (load.seq ((Node.umul (m*m) (full 2) (full 51) (full 0)).seq
      (bcopy (full 2) (full 33) (full 0) (full 1))))
    ∃ (z : HS (66+K) Q prime U) (D : Stacks (66+K) prime) (t : ℕ) (out : Fin ((prime^(w+1))^(m+m)*W) → ZMod 2), z.user = u.user ∧ t ≤ ordinarySetupTime m r w H (prefixes j).length + (budget+overhead*((prime^(w+1))^(m+m)*W)) ∧
      Exec body (prepare.seq (hostedGoodRecordAt cap full full proc prime r (m-r) proj.rank_le_height)) (mk u S) t (mk z D) ∧
      let bank := adapterBank.trans (parent.trans (parentWithWeights.trans full))
      let host := head.trans bank
      HeadColumnReady (d := m+m) (W := W) ((coeff true).trans host) (entry.trans bank) H J []
        (List.ofFn fun i => binSyms H (weights i).val).flatten [] SparseRoleCircuit.encode
        (fun _ => blank) (fun _ => blank) 0 0 out D ∧ D.R (bank 27) = [] ∧
      (∀ push, mnProgPush prepare ≤ push → (∀ f, mnProgPush (body f) ≤ push) →
        ∀ i, 58 ≤ i.val →
          let growth := push*ordinarySetupTime m r w H (prefixes j).length +
            goodRecordStackGrowth (U := U) (A := prime) (GoodChildLayout.parent.trans (parentWithWeights.trans full))
              prime w W H J r proj.rank_le_height
          (D.L i).length ≤ growth ∧ (D.R i).length ≤ growth) ∧
      (∀ i, i.val < 58 → i ≠ full 24 → D.R i = S.R i) ∧
      ∀ x j, let y := transform (diagonal weights) 1 (revExchangeOf (rev m) G
              (transform (diagonal fun i => Ring.inverse (weights i)) 1 x))
             out (index (Fin.append y.1 y.2) j) = word (index (Fin.append x.1 x.2) j) := by
  intro m K src full r slots tmp program g M G clear word payload installed load prepare
  obtain ⟨minor,y,B,l,hy,hl,setup,headReady,empty,one,clock,free,temps,extra,inverses,length,pivots,pair,publicFrame⟩ :=
    ordinaryGeneratedSetup_exec v proj weights prefixes tail schedules hm poolFits unit room body u S j js ready live clear word payload
  obtain ⟨z,F,n,out,hz,hn,run,restored,blankPort,childFrame,childGrowth,correct⟩ := installed minor y B word (preserved B (fun i hi => publicFrame i (by omega)))
    headReady empty one clock free temps extra inverses length pivots pair
  refine ⟨z,F,_,out,hz.trans hy,Nat.add_le_add hl hn,Exec.seq setup run,restored,blankPort,?_,?_,correct⟩
  · intro push hp hb i hi
    have off : i ≠ full 24 := by
      intro eq
      subst i
      change 58 ≤ 24 at hi
      omega
    obtain ⟨left,right⟩ := childGrowth i off
    have preL := exec_stack_length setup hp hb (.lt i)
    have preR := exec_stack_length setup hp hb (.rt i)
    change (B.L i).length ≤ (S.L i).length+push*l at preL
    change (B.R i).length ≤ (S.R i).length+push*l at preR
    obtain ⟨emptyL,emptyR⟩ := ready.2.2.1 i hi
    simp only [emptyL,emptyR,List.length_nil,Nat.zero_add] at preL preR
    exact ⟨left.trans (Nat.add_le_add_right (preL.trans (Nat.mul_le_mul_left push hl)) _),
      right.trans (Nat.add_le_add_right (preR.trans (Nat.mul_le_mul_left push hl)) _)⟩
  intro i hi off
  by_cases base : i = full 2
  · subst i; exact restored.base.trans (headReady.base.symm.trans (publicFrame _ (lt_trans hi (by decide : 58 < 66))))
  by_cases onePort : i = full 28
  · subst i; exact restored.one.trans (headReady.one.symm.trans (publicFrame _ (lt_trans hi (by decide : 58 < 66))))
  by_cases widthPort : i = full 53
  · subst i; exact restored.width.trans (headReady.width.symm.trans (publicFrame _ (lt_trans hi (by decide : 58 < 66))))
  have outside (k : Fin 58) (hk : 58 ≤ (entrySlot k).val ∨ k = 2 ∨ k = 24 ∨ k = 28 ∨ k = 53) :
      full k ≠ i := by
    rcases hk with large | rfl | rfl | rfl | rfl
    · intro eq; rw [← eq] at hi; change (entrySlot k).val < 58 at hi; omega
    · exact Ne.symm base
    · exact off.symm
    · exact Ne.symm onePort
    · exact Ne.symm widthPort
  let bounds (k : Fin 58) : Prop := 58 ≤ (entrySlot k).val ∨ k = 2 ∨ k = 24 ∨ k = 28 ∨ k = 53
  let bank := adapterBank.trans (parent.trans (parentWithWeights.trans (Function.Embedding.refl (Fin 58))))
  have hs : ∀ k, bounds (((shear.trans head).trans bank) k) := by decide
  have ht : ∀ k, bounds (((shear.trans ordinaryHead).trans bank) k) := by decide
  exact (childFrame i (fun k => outside _ (hs k)) (fun k => outside _ (ht k))).2.trans (publicFrame _ (lt_trans hi (by decide : 58 < 66)))

/-- A fixed stopped-child body works at every precision and live ordinary label
after extending the directory workspace by its private tapes. -/
def OrdinaryDirectoryBody [M8.Machine.Net] {N Q d : ℕ} (U : Type) (cap : 217 ≤ Q)
    (proj : Matrix (Fin (d+1)) (Fin (d+1)) ℚ) (full : Fin 58 ↪ Fin N) : Prop :=
  ∃ body : Unit → Pr Unit N Q prime U, ∃ C : ℝ, ∃ overhead : ℕ, ∀ w W,
    let m := d+1
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩
    ∃ budget : ℕ, (0 < W → (budget : ℝ) ≤ C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(M^(m+m)*W : ℕ)) ∧
      ∀ j, LabelStock.live m (w+1) 1 j = true →
      let g := physicalLabel m (w+1) j
      let P := IntegerMultBounds.Swap.Modular.reduce M proj
      fallbackBit proj.rank_le_height P g = false →
      ∀ weights : Fin m → ZMod M, (∀ i, IsUnit (weights i)) → 0 < W →
      ∀ minor, OrdinaryRecordExec (W := W) (H := M.size) (J := W.size) cap proj.rank_le_height
        full body overhead budget (g*P*g⁻¹) minor weights

theorem ordinaryDirectoryBody_exists [M8.Machine.Net] {Q d common work : ℕ} {U : Type}
    (cap : 217 ≤ Q) (proj : Matrix (Fin (d+1)) (Fin (d+1)) ℚ)
    (room : 58 ≤ common+24+31+work)
    (stopped : Record.StoppedDirectoryRun (U := U) cap proj (ordinaryCaller room)) :
    ∃ T, OrdinaryDirectoryBody U cap proj (ordinaryCaller (K := common+24+31+(work+T)) (by omega)) := by
  obtain ⟨T,body,C,overhead,run⟩ := stopped
  let caller := ordinaryCaller room
  let full := caller.trans (Fin.castAddEmb T)
  have installed : OrdinaryDirectoryBody U cap proj full := by
    refine ⟨body,C,overhead,fun w W => ?_⟩
    let M := prime^(w+1)
    obtain ⟨budget,price,execute⟩ := run w W M.size W.size
    refine ⟨budget,price rfl rfl,?_⟩
    intro j live g P clear weights unit hW minor
    obtain ⟨_,record⟩ := execute j live clear
    have call := record weights (fun i => Ring.inverse (weights i))
      (fun i => Ring.mul_inverse_cancel _ (unit i)) (Nat.size_le.mp (le_refl _)) (Nat.size_le.mp (le_refl _))
      hW [] [] [] [] [] (fun _ => blank) 0 (fun _ _ _ => rfl)
    exact ordinaryPreparedRun_exec cap proj.rank_le_height caller body C overhead budget _ minor weights
      (by omega) rfl rfl call
  have transport (N) (eq : (66+(common+24+31+work))+T = N) :
      OrdinaryDirectoryBody U cap proj (full.trans (Fin.castLEEmb eq.le)) := by
    subst N
    exact installed
  have total : (66+(common+24+31+work))+T = 66+(common+24+31+(work+T)) := by omega
  have slots : full.trans (Fin.castLEEmb total.le) = ordinaryCaller (K := common+24+31+(work+T)) (by omega) := by
    ext i
    rfl
  exact ⟨T,slots ▸ transport _ total⟩

def ordinaryCursorPorts : Fin 6 ↪ Fin 66 := ⟨![47,45,46,49,50,51],by decide⟩

open IntegerMultBounds.MathlibTM2.Fast.Main in
/-- Consume the current directory entry and reclaim the ordinary branch's workspace. -/
theorem ordinaryFinish_exec {K Q m w W H J N : ℕ} {P U : Type}
    (body : P → Pr P (66+K) Q prime U) (prog : Pr P (66+K) Q prime U)
    (v : RecursiveInterchangeLayout.Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (weights : Fin m → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (schedule : List ℕ → List (Fin (prime+4)))
    (j : ℕ) (js : List ℕ) (ordinary : schedule (j::js) = schedule js)
    (u y : HS (66+K) Q prime U) (S D : Stacks (66+K) prime) (n push : ℕ)
    (word : Fin N → ZMod 2) (user : y.user = u.user)
    (run : Exec body prog (mk u S) n (mk y D))
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedule S (j::js)) :
    let caller := Fin.castAddEmb (n := 66) K
    let r := ordinaryCursorPorts.trans caller
    let step := prog.seq (readWithSuccessorClock (r 1) (advanceDirectory m r))
    let work := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    let elapsed := n+(1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1))
    mnProgPush step ≤ push → (∀ f, mnProgPush (body f) ≤ push) →
    (∀ i, i.val < 58 → i ≠ caller 24 → D.R i = S.R i) →
    RecordPayload (caller 24) (fun _ => blank) 0 word D →
    ∃ z F t, z.user = u.user ∧ t = elapsed+((work.map fun i => 4*(D.L i).length+2*(D.R i).length+4).sum+1) ∧
      t ≤ elapsed+(4*work.length+1+work.length*(6*(push*elapsed))) ∧
      Exec body (step.seq (clearWorkTapes work)) (mk u S) t (mk z F) ∧
      DirectoryReady v proj w W H J weights prefixes tail schedule F js ∧
      RecordPayload (caller 24) (fun _ => blank) 0 word F ∧
      ∀ k : Fin 66, k.val < 58 → k ≠ 46 → k ≠ 24 → F.R (caller k) = S.R (caller k) := by
  intro caller r step work elapsed hp hb frame payload
  obtain ⟨stream,lens,clean,scratch,matrix,base,one,width,headers,unit,clock,parent,queue⟩ := ready
  have kept (k : Fin 66) (h : k.val < 58) (off : k ≠ 24) := frame (caller k) h (caller.injective.ne off)
  obtain ⟨x,hx,advance⟩ := advanceDirectoryRecord_exec body r m w j prefixes js tail y D
    ((kept 46 (by decide) (by decide)).trans stream)
    ((congrArg List.length (kept 47 (by decide) (by decide))).trans (lens j (by simp)))
    ((congrArg List.length (kept 45 (by decide) (by decide))).trans clock)
    ((kept 49 (by decide) (by decide)).trans scratch)
  let rest := js.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail
  let B := {D with R := Function.update D.R (caller 46) rest}
  have exec : Exec body step (mk u S) elapsed (mk x B) := Exec.seq run advance
  obtain ⟨z,F,t,hz,exactTime,price,finish,publicTape,privateTape⟩ := Record.clearPrivateAfter 58 body step u x S B elapsed push exec hp hb clean
  have stock := List.map_congr_left (l := work)
    (f := fun i => 4*(B.L i).length+2*(B.R i).length+4)
    (g := fun i => 4*(D.L i).length+2*(D.R i).length+4) (fun i hi => by
      have privateTape : 58 ≤ i.val := (List.mem_filter.mp hi).2 |> of_decide_eq_true
      have off : i ≠ caller 46 := by
        intro eq
        subst i
        change 58 ≤ 46 at privateTape
        omega
      simp only [B,Function.update_of_ne off])
  rw [stock] at exactTime
  have same (k : Fin 66) (h : k.val < 58) (cursor : k ≠ 46) (off : k ≠ 24) :=
    ((publicTape (caller k) h).2.trans (Function.update_of_ne (caller.injective.ne cursor) ..)).trans (kept k h off)
  refine ⟨z,F,t,hz.trans (hx.trans user),exactTime,price,finish,?_,?_,same⟩
  · obtain ⟨suffix,mat⟩ := matrix
    refine ⟨((publicTape (caller 46) (by change 46 < 58; decide)).2.trans (Function.update_self (caller 46) rest D.R)),
      fun k hk => (congrArg List.length (same 47 (by decide) (by decide) (by decide))).trans (lens k (List.mem_cons_of_mem _ hk)),
      privateTape,(same 49 (by decide) (by decide) (by decide)).trans scratch,
      ⟨suffix,(same 48 (by decide) (by decide) (by decide)).trans mat⟩,
      (same 2 (by decide) (by decide) (by decide)).trans base,(same 28 (by decide) (by decide) (by decide)).trans one,
      (same 53 (by decide) (by decide) (by decide)).trans width,?_,
      (same 44 (by decide) (by decide) (by decide)).trans unit,
      (congrArg List.length (same 45 (by decide) (by decide) (by decide))).trans clock,
      (same 55 (by decide) (by decide) (by decide)).trans parent,(same 54 (by decide) (by decide) (by decide)).trans (queue.trans ordinary)⟩
    intro k
    have bounds := (by decide : ∀ k : Fin 6, let i := (k.natAdd 33).castLE (by decide : 39 ≤ 66)
      i.val < 58 ∧ i ≠ 46 ∧ i ≠ 24) k
    exact (same _ bounds.1 bounds.2.1 bounds.2.2).trans (headers k)
  · intro k
    have h := publicTape (caller 24) (by change 24 < 58; decide)
    have right := h.2.trans (Function.update_of_ne (caller.injective.ne (by decide : (24 : Fin 66) ≠ 46)) rest D.R)
    rw [h.1,right]
    exact payload k

noncomputable def ordinaryRowCore [M8.Machine.Net] {Q common work : ℕ} {P U : Type} (cap : 217 ≤ Q)
    (m r : ℕ) (hr : r ≤ m) (poolFits : (RingFormula.conjugationDepth m+1)*13 ≤ work)
    (room : 58 ≤ common+24+31+work) (proc : P := by exact ()) : Pr P (66+(common+24+31+work)) Q prime U :=
    let K := common+24+31+work
    let src := directoryRecordMatrixSlot common work
    let full := ordinaryCaller room
    let slots := stageBank (pivotSlots.trans full) r
    let tmp := (59 : Fin 66).castAdd K
    let program : Pr P (66+K) Q prime U :=
      ((directoryRecordWriter m common poolFits).seq (if src = slots 15 then .act .done
        else moveRightOrdered src tmp (slots 15))).seq (goodWeights prime r hr slots : Pr P (66+K) Q prime U)
    let load : Pr P (66+K) Q prime U := packReciprocals prime (ordinaryReciprocalPorts.trans full) (full 54) (List.finRange m)
    ((program.seq (load.seq ((Node.umul (m*m) (full 2) (full 51) (full 0)).seq
        (bcopy (full 2) (full 33) (full 0) (full 1))))).seq (hostedGoodRecordAt cap full full proc prime r (m-r) hr))

noncomputable def ordinaryRowTime (m r w W H prefixLength overhead budget : ℕ) : ℕ :=
  ordinarySetupTime m r w H prefixLength + (budget+overhead*((prime^(w+1))^(m+m)*W))

open IntegerMultBounds.MathlibTM2.Fast.Main in
theorem ordinaryRow_exec [M8.Machine.Net] {d w W H J Q common work : ℕ} {P U : Type}
    (proc : P) (cap : 217 ≤ Q) (overhead budget : ℕ)
    (v : RecursiveInterchangeLayout.Descriptor) (proj : Matrix (Fin (d+1)) (Fin (d+1)) ℚ)
    (weights : Fin (d+1) → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (schedules : List ℕ → List (Fin (prime+4)))
    (hm : prime^(w+1) < 2^H) (poolFits : (RingFormula.conjugationDepth (d+1)+1)*13 ≤ work)
    (unit : ∀ i, IsUnit (weights i))
    (room : 58 ≤ common+24+31+work)
    (body : P → Pr P (66+(common+24+31+work)) Q prime U) (u : HS (66+(common+24+31+work)) Q prime U) (S : Stacks (66+(common+24+31+work)) prime) (j : ℕ) (js : List ℕ)
    (bodyPush : ℕ) (pushBound : ∀ f, mnProgPush (body f) ≤ bodyPush)
    (context : Stacks (66+(common+24+31+work)) prime → Prop)
    (preserved : ∀ D, (∀ i, i.val < 58 → D.R i = S.R i) → context D)
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedules S (j::js))
    (queue : schedules (j::js) = schedules js)
    (live : LabelStock.live (d+1) (w+1) 1 j = true) :
    letI : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩
    let m := d+1
    let K := common+24+31+work
    let caller := Fin.castAddEmb (n := 66) K
    let full := ordinaryCaller room
    let g := physicalLabel m (w+1) j
    let M := IntegerMultBounds.Swap.Modular.reduce (prime^(w+1)) proj
    let G := g*M*g⁻¹
    fallbackBit proj.rank_le_height M g = false →
    ∀ word : Fin ((prime^(w+1))^(m+m)*W) → ZMod 2,
    RecordPayload (caller 24) (fun _ => blank) 0 word S →
    (∀ minor, OrdinaryRecordExec (W := W) (H := H) (J := J) cap proj.rank_le_height full body overhead budget G minor weights proc context) →
    let core := ordinaryRowCore (U := U) cap m proj.rank proj.rank_le_height poolFits room proc
    let ports := ordinaryCursorPorts.trans caller
    let step := core.seq (readWithSuccessorClock (ports 1) (advanceDirectory m ports))
    let scratch := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    let elapsed := ordinaryRowTime m proj.rank w W H (prefixes j).length overhead budget +
      (1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1))
    let push := max (mnProgPush step) bodyPush
    let growth := push*ordinarySetupTime m proj.rank w H (prefixes j).length +
      goodRecordStackGrowth (U := U) (A := prime) (GoodChildLayout.parent.trans (parentWithWeights.trans full))
        prime w W H J proj.rank proj.rank_le_height
    ∃ z F t out, z.user = u.user ∧ t ≤ elapsed+(4*scratch.length+1+scratch.length*(6*(push*elapsed))) ∧
      t ≤ elapsed+(scratch.length*(6*growth+4)+1) ∧
      Exec body (step.seq (clearWorkTapes scratch)) (mk u S) t (mk z F) ∧
      DirectoryReady v proj w W H J weights prefixes tail schedules F js ∧
      RecordPayload (caller 24) (fun _ => blank) 0 out F ∧
      (∀ k : Fin 66, k.val < 58 → k ≠ 46 → k ≠ 24 → F.R (caller k) = S.R (caller k)) ∧
      ∀ x j, let y := transform (diagonal weights) 1 (revExchangeOf (rev m) G
              (transform (diagonal fun i => Ring.inverse (weights i)) 1 x))
             out (index (Fin.append y.1 y.2) j) = word (index (Fin.append x.1 x.2) j) := by
  intro m K caller full g M G clear word payload installed core ports step scratch elapsed push growth
  obtain ⟨y,D,n,out,hy,hn,exec,restored,_,stock,frame,correct⟩ :=
    ordinaryGeneratedRecord_exec cap overhead budget v proj weights prefixes tail schedules hm poolFits unit room
      body u S j js ready live proc context preserved clear word (by
        intro k
        change _ = readAt blank (S.L (caller 24)) (S.R (caller 24)) k
        simpa only [sub_zero,List.map_ofFn] using (payload k).symm) installed
  obtain ⟨z,F,t,hz,exactTime,ht,finish,next,output,kept⟩ := ordinaryFinish_exec body core v proj weights prefixes tail
    schedules j js queue u y S D n push out hy exec ready (le_max_left ..) (fun f => (pushBound f).trans (le_max_right ..)) frame
    (by intro k
        have output := (restored.src k).symm
        change readAt blank (D.L (caller 24)) (D.R (caller 24)) (k-0) = _ at output
        simpa only [List.map_ofFn] using output)
  have cleanBound : ∀ i ∈ scratch, 4*(D.L i).length+2*(D.R i).length+4 ≤ 6*growth+4 := by
    intro i hi
    have before := stock push (le_trans (le_max_left ..) (le_trans (le_max_left ..) (le_max_left ..)))
      (fun f => (pushBound f).trans (le_max_right ..)) i (of_decide_eq_true (List.mem_filter.mp hi).2)
    change (D.L i).length ≤ growth ∧ (D.R i).length ≤ growth at before
    omega
  have cleared := List.sum_le_sum cleanBound
  simp only [List.map_const',List.sum_replicate,smul_eq_mul] at cleared
  have localTime : t ≤ elapsed+(scratch.length*(6*growth+4)+1) := by
    rw [exactTime]
    exact Nat.add_le_add (Nat.add_le_add_right hn _) (Nat.add_le_add_right cleared 1)
  refine ⟨z,F,t,out,hz,ht.trans ?_,localTime,finish,next,output,kept,correct⟩
  have bound : n ≤ ordinaryRowTime m proj.rank w W H (prefixes j).length overhead budget := hn
  apply Nat.add_le_add (Nat.add_le_add_right bound _)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (Nat.add_le_add_right bound _)))) _

/-- Padding consumes one directory entry. It preserves the payload, selectors,
and the blank workspace needed by the next live record. -/
theorem ordinaryPadding_exec {K Q m w W H J : ℕ} {P U : Type}
    (body : P → Pr P (66+K) Q prime U)
    (v : RecursiveInterchangeLayout.Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (weights : Fin m → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (schedule : List ℕ → List (Fin (prime+4)))
    (j : ℕ) (js : List ℕ) (skip : schedule (j::js) = schedule js)
    (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime)
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedule S (j::js)) :
    let caller := Fin.castAddEmb (n := 66) K
    let r := ordinaryCursorPorts.trans caller
    let rest := js.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail
    let F := {S with R := Function.update S.R (caller 46) rest}
    ∃ z, z.user = u.user ∧ Exec body (readWithSuccessorClock (r 1) (advanceDirectory m r))
      (mk u S) (1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)) (mk z F) ∧
      DirectoryReady v proj w W H J weights prefixes tail schedule F js := by
  intro caller r rest F
  obtain ⟨stream,widths,privateBank,empty,⟨suffix,matrix⟩,base,one,width,headers,unit,clock,parent,queue⟩ := ready
  obtain ⟨z,user,run⟩ := advanceDirectoryRecord_exec body r m w j prefixes js tail u S
    stream (widths j (by simp)) clock empty
  have keep (k : Fin 66) (off : k ≠ 46) : F.R (caller k) = S.R (caller k) :=
    Function.update_of_ne (caller.injective.ne off) ..
  refine ⟨z,user,run,Function.update_self (caller 46) rest S.R,
    fun k hk => (congrArg List.length (keep 47 (by decide))).trans (widths k (List.mem_cons_of_mem _ hk)),?_,
    (keep 49 (by decide)).trans empty,⟨suffix,(keep 48 (by decide)).trans matrix⟩,
    (keep 2 (by decide)).trans base,(keep 28 (by decide)).trans one,(keep 53 (by decide)).trans width,?_,
    (keep 44 (by decide)).trans unit,(congrArg List.length (keep 45 (by decide))).trans clock,
    (keep 55 (by decide)).trans parent,(keep 54 (by decide)).trans (queue.trans skip)⟩
  · intro i hi
    have off : i ≠ caller 46 := by intro eq; rw [eq] at hi; change 58 ≤ 46 at hi; omega
    exact ⟨(privateBank i hi).1,(Function.update_of_ne off ..).trans (privateBank i hi).2⟩
  · intro k
    exact (keep _ ((by decide : ∀ k : Fin 6, (k.natAdd 33).castLE (by decide : 39 ≤ 66) ≠ 46) k)).trans (headers k)

open IntegerMultBounds.MathlibTM2.Fast.Main in
theorem ordinaryOrPadding_exec [M8.Machine.Net] {d w W H J Q common work : ℕ} {P U : Type}
    (proc : P) (cap : 217 ≤ Q) (overhead budget : ℕ)
    (v : RecursiveInterchangeLayout.Descriptor) (proj : Matrix (Fin (d+1)) (Fin (d+1)) ℚ)
    (weights : Fin (d+1) → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (schedules : List ℕ → List (Fin (prime+4)))
    (hm : prime^(w+1) < 2^H) (poolFits : (RingFormula.conjugationDepth (d+1)+1)*13 ≤ work)
    (unit : ∀ i, IsUnit (weights i))
    (room : 58 ≤ common+24+31+work)
    (body : P → Pr P (66+(common+24+31+work)) Q prime U) (u : HS (66+(common+24+31+work)) Q prime U) (S : Stacks (66+(common+24+31+work)) prime) (j : ℕ) (js : List ℕ)
    (bodyPush : ℕ) (pushBound : ∀ f, mnProgPush (body f) ≤ bodyPush)
    (context : Stacks (66+(common+24+31+work)) prime → Prop)
    (preserved : ∀ D, (∀ i, i.val < 58 → D.R i = S.R i) → context D)
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedules S (j::js))
    (queue : schedules (j::js) = schedules js) :
    letI : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩
    let m := d+1
    let K := common+24+31+work
    let caller := Fin.castAddEmb (n := 66) K
    let full := ordinaryCaller room
    let g := physicalLabel m (w+1) j
    let M := IntegerMultBounds.Swap.Modular.reduce (prime^(w+1)) proj
    let G := g*M*g⁻¹
    let live := LabelStock.live m (w+1) 1 j
    (live = true → fallbackBit proj.rank_le_height M g = false) →
    ∀ word : Fin ((prime^(w+1))^(m+m)*W) → ZMod 2,
    RecordPayload (caller 24) (fun _ => blank) 0 word S →
    (live = true → ∀ minor, OrdinaryRecordExec (W := W) (H := H) (J := J) cap proj.rank_le_height full body overhead budget G minor weights proc context) →
    let core := ordinaryRowCore (U := U) cap m proj.rank proj.rank_le_height poolFits room proc
    let ports := ordinaryCursorPorts.trans caller
    let padding := readWithSuccessorClock (ports 1) (advanceDirectory m ports)
    let step := core.seq padding
    let scratch := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    let elapsed := ordinaryRowTime m proj.rank w W H (prefixes j).length overhead budget +
      (1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1))
    let push := max (mnProgPush step) bodyPush
    let growth := push*ordinarySetupTime m proj.rank w H (prefixes j).length +
      goodRecordStackGrowth (U := U) (A := prime) (GoodChildLayout.parent.trans (parentWithWeights.trans full))
        prime w W H J proj.rank proj.rank_le_height
    ∃ z F t out, z.user = u.user ∧ t ≤ (if live then elapsed+(4*scratch.length+1+scratch.length*(6*(push*elapsed)))
        else 1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)) ∧
      t ≤ (if live then elapsed+(scratch.length*(6*growth+4)+1)
        else 1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)) ∧
      Exec body (if live then step.seq (clearWorkTapes scratch) else padding) (mk u S) t (mk z F) ∧
      DirectoryReady v proj w W H J weights prefixes tail schedules F js ∧
      RecordPayload (caller 24) (fun _ => blank) 0 out F ∧
      (∀ k : Fin 66, k.val < 58 → k ≠ 46 → k ≠ 24 → F.R (caller k) = S.R (caller k)) ∧
      (if live then ∀ x j, let y := transform (diagonal weights) 1 (revExchangeOf (rev m) G
              (transform (diagonal fun i => Ring.inverse (weights i)) 1 x))
             out (index (Fin.append y.1 y.2) j) = word (index (Fin.append x.1 x.2) j) else word = out) := by
  intro m K caller full g M G live accepted word payload installed core ports padding step scratch elapsed push growth
  cases active : live with
  | true =>
    simp only [active,ite_true]
    exact ordinaryRow_exec proc cap overhead budget v proj weights prefixes tail schedules hm poolFits unit room body u S
      j js bodyPush pushBound context preserved ready queue active (accepted active) word payload (installed active)
  | false =>
    simp only [active,Bool.false_eq_true,ite_false]
    obtain ⟨z,user,run,next⟩ := ordinaryPadding_exec body v proj weights prefixes tail schedules j js queue u S ready
    let rest := js.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail
    have keep (k : Fin 66) (off : k ≠ 46) :=
      Function.update_of_ne (caller.injective.ne off) rest S.R
    refine ⟨z,_,_,word,user,le_rfl,le_rfl,run,next,?_,(fun k _ ne _ => keep k ne),rfl⟩
    intro k
    change readAt blank _ (Function.update S.R (caller 46) rest (caller 24)) _ = _
    rw [keep 24 (by decide)]
    exact payload k

end IntegerMultBounds.MathlibTM2.M6.BitNode
