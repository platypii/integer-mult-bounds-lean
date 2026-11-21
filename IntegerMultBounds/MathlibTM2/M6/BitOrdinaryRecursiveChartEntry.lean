module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryDispatch

/-! Place the recursive chart's archive splitter on the live child dimension tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open FlatCoordinateLayout LabelTraversal Matrix M8.Exchange IntegerMultBounds.Swap.Modular

abbrev roleSplitTapes := ((1+142080)+2)+2
abbrev roleSplitWorkspace := roleSplitTapes+12

def dimensionSlots : Fin 4 ↪ Fin roleSplitWorkspace :=
  (Fin.castAddEmb (n := 4) 10).trans (roleSplitCountBank 142080)

def dimensionPorts (K T : ℕ) (room : 16 ≤ T) : Fin 4 ↪ Fin (66+(K+3+T)) :=
  let dim : Fin 4 → Fin 9 := ![5,3,1,2]
  ⟨fun j => childMetadataSources K T room (dim j),by
    intro i j eq
    have h := congrArg Fin.val eq
    fin_cases i <;> fin_cases j <;> first | rfl | (simp [dim,childMetadataSources,stoppedChartPrivate] at h <;> omega)⟩

noncomputable def recursiveRoleSplitPlacement {n K T : ℕ} (room : 16 ≤ T)
    (replay : Fin (66+(K+3+T)) ↪ Fin n) : Fin roleSplitWorkspace ↪ Fin (n+roleSplitWorkspace) :=
  returnChartBank dimensionSlots ((dimensionPorts K T room).trans replay)

private theorem split_body_private (i : Fin roleSplitTapes) (j : Fin 4) : dimensionSlots j ≠ i.castAdd 12 := by
  intro eq
  have h := congrArg Fin.val eq
  have value : (dimensionSlots j).val = roleSplitTapes+j.val := by fin_cases j <;> rfl
  rw [value] at h
  change roleSplitTapes+j.val = i.val at h
  omega

/-- All splitter tapes are in the appended bank. Four of the arithmetic
routine's inputs alias live headers in the caller; its remaining tapes are private. -/
theorem recursiveRoleSplit_layout {n K T : ℕ} (room : 16 ≤ T) (replay : Fin (66+(K+3+T)) ↪ Fin n) :
    let place := recursiveRoleSplitPlacement room replay
    let r := (roleSplitCountBank 142080).trans place
    let src := fun j => (replay (childMetadataSources K T room j)).castAdd roleSplitWorkspace
    (∀ i : Fin roleSplitTapes, place (i.castAdd 12) = (i.castAdd 12).natAdd n) ∧
    r 0 = src 5 ∧ r 1 = src 3 ∧ r 2 = src 1 ∧ r 3 = src 2 ∧
    ∀ i : Fin 14, 4 ≤ i.val → r i = ((roleSplitCountBank 142080) i).natAdd n := by
  intro place r src
  have shared (j : Fin 4) := returnChartBank_selected dimensionSlots ((dimensionPorts K T room).trans replay) j
  refine ⟨fun i => returnChartBank_private _ _ _ (split_body_private i),shared 0,shared 1,shared 2,shared 3,?_⟩
  intro i hi
  apply returnChartBank_private
  intro j
  apply (roleSplitCountBank 142080).injective.ne
  intro eq
  have h := congrArg Fin.val eq
  change j.val = i.val at h
  omega

/-- Use the unused private image of the first two shared dimension slots for
the chart loader's copy scratch. -/
def roleLoaderScratch (n : ℕ) (i : Fin 2) : Fin (n+roleSplitWorkspace) :=
  (dimensionSlots (i.castAdd 2)).natAdd n

private theorem releaseSplitWorkspace_exec {n tapes Q : ℕ} {P U : Type} (body : P → Pr P (n+tapes) Q prime U)
    (p : Pr P (n+tapes) Q prime U) (u v : HS (n+tapes) Q prime U)
    (S F : Stacks (n+tapes) prime) (t c : ℕ) (run : Exec body p (mk u S) t (mk v F))
    (hp : Fast.Main.mnProgPush p ≤ c) (hb : ∀ f, Fast.Main.mnProgPush (body f) ≤ c)
    (free : ∀ i : Fin tapes, S.L (i.natAdd n) = [] ∧ S.R (i.natAdd n) = []) :
    let work := (List.finRange tapes).map (Fin.natAddEmb n)
    ∃ z B m, z.user = v.user ∧ m ≤ tapes*(6*(c*t)+4)+1 ∧
      Exec body (clearWorkTapes work) (mk v F) m (mk z B) ∧
      embStk (Fin.castAddEmb tapes) B = embStk (Fin.castAddEmb tapes) F ∧
      ∀ i : Fin tapes, B.L (i.natAdd n) = [] ∧ B.R (i.natAdd n) = [] := by
  intro work
  obtain ⟨z,user,clear⟩ := clearWorkTapes_exec body work ((List.nodup_finRange _).map (Fin.natAddEmb n).injective) v F
  have price (j) (hj : j ∈ work) : 4*(F.L j).length+2*(F.R j).length+4 ≤ 6*(c*t)+4 := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    have l := exec_stack_length run hp hb (.lt (i.natAdd n))
    have r := exec_stack_length run hp hb (.rt (i.natAdd n))
    change (F.L _).length ≤ (S.L _).length+c*t at l
    change (F.R _).length ≤ (S.R _).length+c*t at r
    rw [(free i).1] at l
    rw [(free i).2] at r
    change 4*(F.L (i.natAdd n)).length+2*(F.R (i.natAdd n)).length+4 ≤ _
    simp only [List.length_nil,zero_add] at l r
    omega
  have total := List.sum_le_sum price
  simp only [List.map_const',List.sum_replicate_nat,List.length_map,List.length_finRange,work] at total
  have outside (j : Fin n) : j.castAdd tapes ∉ work := by
    intro h
    obtain ⟨i,_,eq⟩ := List.mem_map.mp h
    have bad := congrArg Fin.val eq
    change n+i.val = j.val at bad
    omega
  refine ⟨z,_,_,user,Nat.add_le_add_right total 1,clear,?_,?_⟩
  · apply Stacks.ext
    · rfl
    · rfl
    · funext i; exact ite_eq_right (outside i)
    · funext i; exact ite_eq_right (outside i)
  · intro i
    have h : i.natAdd n ∈ work := List.mem_map_of_mem (List.mem_finRange i)
    simp only [ite_eq_left h,and_self]

/-- Clear entry metadata after a framed child returns. Charge the words still on the scanner
when the child returns, including any metadata produced by the child. -/
theorem recursiveChartReturn_exec {n s Q : ℕ} {P U : Type}
    (body : P → Pr P n Q prime U) (entry child : Pr P n Q prime U)
    (scanner : Fin s ↪ Fin n) (owner : Fin n) (off : ∀ i, scanner i ≠ owner)
    {u v z : HS n Q prime U} {S F G : Stacks n prime} {t m : ℕ}
    (entered : Exec body entry (mk u S) t (mk v F))
    (called : Exec body child (mk v F) m (mk z G))
    (free : ∀ i, S.L (scanner i) = [] ∧ S.R (scanner i) = [])
    (outside : ∀ j, (∀ i, scanner i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j)
    (framed : ∀ j, j ≠ owner → (∀ i, scanner i ≠ j) → G.L j = F.L j ∧ G.R j = F.R j) :
    let work := (List.finRange s).map scanner
    let k := (work.map (fun j => 4*(G.L j).length+2*(G.R j).length+4)).sum+1
    ∃ y B, y.user = z.user ∧
      Exec body ((entry.seq child).seq (clearWorkTapes work)) (mk u S) (t+m+k) (mk y B) ∧
      B.L owner = G.L owner ∧ B.R owner = G.R owner ∧
      ∀ j, j ≠ owner → B.L j = S.L j ∧ B.R j = S.R j := by
  intro work k
  obtain ⟨y,user,clear⟩ := clearWorkTapes_exec body work ((List.nodup_finRange _).map scanner.injective) z G
  have mem (j) : j ∈ work ↔ ∃ i, scanner i = j := by simp [work]
  have ownerOff : owner ∉ work := fun h => by obtain ⟨i,eq⟩ := (mem _).mp h; exact off i eq
  refine ⟨y,_,user,Exec.seq (Exec.seq entered called) clear,
    ite_eq_right ownerOff,ite_eq_right ownerOff,?_⟩
  intro j ne
  by_cases h : j ∈ work
  · obtain ⟨i,rfl⟩ := (mem _).mp h
    simp [h,(free i).1,(free i).2]
  · have keep := outside j (fun i eq => h ((mem _).mpr ⟨i,eq⟩))
    have held := framed j ne (fun i eq => h ((mem _).mpr ⟨i,eq⟩))
    exact ⟨(ite_eq_right h).trans (held.1.trans keep.1),(ite_eq_right h).trans (held.2.trans keep.2)⟩

/-- Keep the child's data on its owner tapes and take the surrounding chart
registers from the caller's reusable workspace. -/
def recursiveEntryPlacement {n K T s k back : ℕ}
    (replay : Fin (66+(K+3+T)) ↪ Fin n) (fits : (s+5)+back ≤ K)
    (owners : Fin k ↪ Fin n)
    (apart : ∀ i j, owners i ≠ replay (directoryChildWorkspace K T j)) :
    Fin (((s+5)+k)+back) ↪ Fin n := by
  let work := ((Fin.castLEEmb fits).trans (directoryChildWorkspace K T)).trans replay
  let front := (Fin.castAddEmb (n := s+5) back).trans work
  let tail := (Fin.natAddEmb (s+5) (m := back)).trans work
  refine ⟨Fin.addCases (Fin.addCases front owners) tail,?_⟩
  have distinct (i j) : front i ≠ tail j := by
    apply work.injective.ne
    intro eq
    have h := congrArg Fin.val eq
    change i.val = (s+5)+j.val at h
    omega
  have left (i j) : owners i ≠ front j := apart _ _
  have right (i j) : owners i ≠ tail j := apart _ _
  intro i j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  case left.left i j =>
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [Fin.addCases_left,Fin.addCases_right,front.injective.eq_iff,owners.injective.eq_iff,
        left,fun i j => (left i j).symm]
  case left.right i j =>
    induction i using Fin.addCases <;> simp [distinct,right]
  case right.left i j =>
    induction j using Fin.addCases <;> simp [fun i j => (distinct i j).symm,fun i j => (right i j).symm]
  case right.right i j => simp [tail.injective.eq_iff]

/-- Install the child chart in the caller with a fixed splitter placement.
The nine sources and cutoff are the actual replay ports. -/
theorem recursiveRoleChartEntry_exec {n K T Q s k back w : ℕ} {P U : Type}
    {Label : Type} (room : 16 ≤ T) (replay : Fin (66+(K+3+T)) ↪ Fin n)
    (owners : Fin k ↪ Fin n) (reserve : (s+5)+back ≤ K) (space : 59 ≤ s)
    (apart : ∀ i j, owners i ≠ replay (directoryChildWorkspace K T j))
    (body : P → Pr P (n+roleSplitWorkspace) Q prime U)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (layout : RecursiveInterchangeLayout.Descriptor) (rows width : ℕ) (splitRows : layout.rows = 142080*rows)
    (role : Fin 142080) (archive : ℕ → List (Fin (prime+4)))
    (outer : 0 < layout.beforeRows) (rowCount : 0 < rows) (labels : 0 < layout.beforeH)
    (positive : 0 < layout.between*layout.afterD)
    (aligned : layout.width = 64*(w+1)) (fits : width ≤ prime^layout.width)
    (widths : ∀ i < layout.beforeRows*rows*142080*layout.beforeH, (archive i).length = width)
    (clean : ∀ i < layout.beforeRows*rows*142080*layout.beforeH, blank ∉ archive i)
    (u : HS (n+roleSplitWorkspace) Q prime U) (S : Stacks (n+roleSplitWorkspace) prime) :
    let W := layout.between*layout.afterD
    let a := layout.beforeRows
    let H := layout.beforeH
    let lift := Fin.castAddEmb (n := n) roleSplitWorkspace
    let place := recursiveEntryPlacement replay reserve owners apart
    let privateBank := (((Fin.castLEEmb reserve).trans (directoryChildWorkspace K T)).trans replay).trans lift
    let full := place.trans lift
    let split := recursiveRoleSplitPlacement room replay
    let sources := fun j => lift (replay (childMetadataSources K T room j))
    let cut := lift (replay ((40 : Fin 66).castAdd (K+3+T)))
    let scratch := roleLoaderScratch n
    let select : Pr P (n+roleSplitWorkspace) Q prime U := childRoleQueueProgram capacity split (sources 8) role
    let localBank := ((Fin.castAddEmb (n := s) 5).trans (Fin.castAddEmb k)).trans (Fin.castAddEmb back)
    let scanner := localBank.trans full
    let chart := ((Fin.natAddEmb (s+5) (m := k)).trans (Fin.castAddEmb back)).trans full
    let dst := (ordinaryMetadataPorts.trans (Fin.castLEEmb space)).trans scanner
    let port := (((role.natAdd 1).castAdd 2).castAdd 2)
    let source := Function.update sources 8 ((port.castAdd 12).natAdd n)
    let load : Pr P (n+roleSplitWorkspace) Q prime U := (Record.copyLeafHeaders source dst (scratch 0) (scratch 1) (List.finRange 9)).seq
      (bcopy cut (scanner ((40 : Fin 59).castLE space)) (scratch 0) (scratch 1))
    let work := (List.finRange roleSplitWorkspace).map (Fin.natAddEmb n)
    let V := (prime^(w+1))^128*W
    let weights := fun _ : Fin 64 => (1 : ZMod (prime^(w+1)))
    let queue := directoryChartQueue (some role) H 0 (LabelMask.records (RecursiveInterchangeLayout.role layout 142080)) archive
    (S.R cut).length ≤ layout.width →
    (∀ i, S.R (sources i) = ordinaryEntryWords W a rows H true weights width
      ((List.range (a*rows*142080*H)).flatMap archive) (ordinaryMetadataPorts i).val) →
    (∀ i : Fin roleSplitWorkspace, S.L (i.natAdd n) = [] ∧ S.R (i.natAdd n) = []) →
    (∀ j : Fin K, let i := lift (replay (directoryChildWorkspace K T j)); S.L i = [] ∧ S.R i = []) →
    ∀ c, Fast.Main.mnProgPush (select.seq load) ≤ c → (∀ f, Fast.Main.mnProgPush (body f) ≤ c) →
    let budget := (149*(roleSplitTapes+5)+2417)*(a*rows*142080*H*V)
    ∃ z F t, z.user = u.user ∧ t ≤ budget+roleSplitWorkspace*(6*(c*budget)+4)+1 ∧
      Exec body ((select.seq load).seq (clearWorkTapes work)) (mk u S) t (mk z F) ∧
      ordinaryParentEntry (T := s) back (directoryChartWords (S.R cut) W a rows H true weights width queue)
        (embStk (owners.trans lift) F) = embStk full F ∧
      (∀ i, F.L (lift (owners i)) = S.L (lift (owners i)) ∧ F.R (lift (owners i)) = S.R (lift (owners i))) ∧
      (∀ j : Fin n, (∀ i, scanner i ≠ lift j) → F.L (lift j) = S.L (lift j) ∧ F.R (lift j) = S.R (lift j)) ∧
      (∀ i : Fin roleSplitWorkspace, F.L (i.natAdd n) = [] ∧ F.R (i.natAdd n) = []) ∧
      ∀ (i : Fin k) (programs : Label → Pr Label (((s+5)+k)+back) Q prime U) (label : Label → P)
        (child : Pr Label (((s+5)+k)+back) Q prime U) v G m,
        (∀ f, body (label f) = embProg full label (programs f)) →
        Exec programs child (mk (embDn full z) (embStk full F)) m (mk v G) →
        (∀ l, l ≠ i → let j := (l.natAdd (s+5)).castAdd back
          G.L j = F.L (lift (owners l)) ∧ G.R j = F.R (lift (owners l))) →
        ∃ y B d, y.user = v.user ∧
          Exec body ((((select.seq load).seq (clearWorkTapes work)).seq (embProg full label child)).seq
            (clearWorkTapes ((List.finRange ((s+5)+back)).map privateBank))) (mk u S) (t+m+d) (mk y B) ∧
          B.L (lift (owners i)) = G.L ((i.natAdd (s+5)).castAdd back) ∧
          B.R (lift (owners i)) = G.R ((i.natAdd (s+5)).castAdd back) ∧
          d = chartReturnCost G ∧
          ∀ j, j ≠ lift (owners i) → B.L j = S.L j ∧ B.R j = S.R j := by
  intro W a H lift place privateBank full split sources cut scratch select localBank scanner chart dst port source load work V weights queue cutFits headers free reusable c push bodies budget
  obtain ⟨bank,h₀,h₁,h₂,h₃,privateCount⟩ := recursiveRoleSplit_layout room replay
  let bank' := (Fin.castAddEmb (n := roleSplitTapes) 12).trans split
  have high (j : Fin roleSplitTapes) : bank' j = (j.castAdd 12).natAdd n := bank j
  have disjoint (j : Fin roleSplitWorkspace) (i : Fin n) : j.natAdd n ≠ lift i := by
    intro eq
    have h := congrArg Fin.val eq
    change n+j.val = i.val at h
    omega
  have noWork (j : Fin roleSplitTapes) (i : Fin 2) : bank' j ≠ scratch i := by
    rw [high]
    exact (Fin.natAddEmb n).injective.ne (split_body_private j (i.castAdd 2)).symm
  have scratchNe : scratch 0 ≠ scratch 1 :=
    (Fin.natAddEmb n).injective.ne (dimensionSlots.injective.ne (by decide : ((0 : Fin 2).castAdd 2) ≠ (1 : Fin 2).castAdd 2))
  let frontSlot (j : Fin (s+5)) := (j.castAdd back).castLE reserve
  have frontTape (j : Fin (s+5)) :
      place ((j.castAdd k).castAdd back) = replay (directoryChildWorkspace K T (frontSlot j)) := by
    simp [place,recursiveEntryPlacement,frontSlot]
  have front (j : Fin (s+5)) := reusable (frontSlot j)
  have suffix (j : Fin back) := reusable ((j.natAdd (s+5)).castLE reserve)
  have metadataOff (i : Fin 9) (j : Fin s) :
      replay (childMetadataSources K T room i) ≠ place (localBank j) := by
    change _ ≠ place (((j.castAdd 5).castAdd k).castAdd back)
    rw [frontTape]
    exact replay.injective.ne ((directoryChildWorkspace_off K T room _).1 i)
  have cutoffOff (j : Fin s) :
      replay ((40 : Fin 66).castAdd (K+3+T)) ≠ place (localBank j) := by
    change _ ≠ place (((j.castAdd 5).castAdd k).castAdd back)
    rw [frontTape]
    exact replay.injective.ne (directoryChildWorkspace_off K T room _).2
  have dstLow (i) : dst i = lift (place (localBank (((ordinaryMetadataPorts i).castLE space)))) := rfl
  have srcDst (i j) : source i ≠ dst j := by
    rw [dstLow]
    by_cases eq : i = 8
    · subst i; exact (show source 8 = _ from Function.update_self ..) ▸ disjoint (port.castAdd 12) _
    · rw [show source i = sources i from Function.update_of_ne eq ..]
      exact lift.injective.ne (metadataOff _ _)
  have srcWork (i j) : source i ≠ scratch j := by
    by_cases eq : i = 8
    · subst i
      rw [show source 8 = _ from Function.update_self ..,← high port]
      exact noWork port j
    · rw [show source i = sources i from Function.update_of_ne eq ..]
      exact (disjoint _ _).symm
  have ports (i) : [source i,dst i,scratch 0,scratch 1].Nodup := by
    have dstWork (j) : dst i ≠ scratch j := (disjoint _ _).symm
    simp [srcDst,srcWork,dstWork,scratchNe]
  have radixFits : prime^layout.width ≤ V := by
    change _ ≤ (prime^(w+1))^128*W
    rw [← pow_mul,aligned]
    exact (Nat.pow_le_pow_right Shared50ModularControl.prime_prime.pos (by omega)).trans
      (Nat.le_mul_of_pos_right _ positive)
  have cutoffFits : (S.R cut).length ≤ a*rows*H*V := by
    have digits : layout.width ≤ prime^layout.width := (Nat.lt_two_pow_self (n := layout.width)).le.trans
      (Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le _)
    exact ((cutFits.trans digits).trans radixFits).trans
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos outer rowCount) labels))
  have run := childRoleChartEntry_exec body full space split capacity sources cut (scratch 0) (scratch 1)
    W a rows H width role archive outer rowCount labels positive (fits.trans radixFits) widths clean u S cutoffFits headers
  rw [← show bank' = (Fin.castAddEmb (n := roleSplitTapes) 12).trans split from rfl] at run
  rw [high port] at run
  obtain ⟨z,F,t,user,paid,exec,entry,live,frame⟩ := run (fun j i => (high j).symm ▸ disjoint _ _)
    (fun j i => (high j).symm ▸ disjoint _ _) (fun j => ⟨(high j).symm ▸ disjoint _ _,noWork j 0,noWork j 1⟩)
    srcDst ports (fun i => lift.injective.ne (cutoffOff _)) (by
      change [cut,scanner ((40 : Fin 59).castLE space),scratch 0,scratch 1].Nodup
      have sep : cut ≠ scanner ((40 : Fin 59).castLE space) := lift.injective.ne (cutoffOff _)
      simp [sep,scratchNe,show ∀ i, cut ≠ scratch i from fun i => (disjoint _ _).symm,
        show ∀ i, scanner ((40 : Fin 59).castLE space) ≠ scratch i from fun i => (disjoint _ _).symm])
    (free _).2 (free _).2 (fun j => by simpa [full,frontTape] using front j)
      (fun j => by simpa [full,place,recursiveEntryPlacement] using suffix j) h₀ h₁ h₂ h₃ (fun i hi => (privateCount i hi).symm ▸ (free _).2)
    (fun j => (high j).symm ▸ (free _).1) (fun j => (high j).symm ▸ (free _).2)
  obtain ⟨y,B,m,same,time,clear,base,blank⟩ := releaseSplitWorkspace_exec body (select.seq load) u z S F t c exec push bodies free
  have stay (i : Fin n) : B.L (lift i) = F.L (lift i) ∧ B.R (lift i) = F.R (lift i) :=
    ⟨congrArg (fun Z : Stacks n prime => Z.L i) base,congrArg (fun Z : Stacks n prime => Z.R i) base⟩
  have projected {l : ℕ} (e : Fin l ↪ Fin n) : embStk (e.trans lift) B = embStk (e.trans lift) F :=
    congrArg (embStk e) base
  have ownerChart : chart = owners.trans lift := by
    ext i
    simp [chart,full,place,recursiveEntryPlacement]
  rw [← ownerChart]
  have outside (j : Fin n) (off : ∀ i, scanner i ≠ lift j) :
      B.L (lift j) = S.L (lift j) ∧ B.R (lift j) = S.R (lift j) := by
    have kept := frame _ (fun i => (high i).symm ▸ disjoint _ j) off
    exact ⟨(stay j).1.trans kept.1,(stay j).2.trans kept.2⟩
  refine ⟨y,B,t+m,same.trans user,?_,Exec.seq exec clear,?_,?_,outside,blank,?_⟩
  · have bound : t ≤ budget := paid
    have mt := Nat.mul_le_mul_left roleSplitWorkspace
      (Nat.add_le_add_right (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left c bound)) 4)
    omega
  · rw [projected place]
    have sameChart : embStk chart B = embStk chart F :=
      projected (((Fin.natAddEmb (s+5) (m := k)).trans (Fin.castAddEmb back)).trans place)
    rw [sameChart]
    have records : LabelMask.records (RecursiveInterchangeLayout.role layout 142080) = a*rows*H := by
      simp only [LabelMask.records,RecursiveInterchangeLayout.role,splitRows,Nat.mul_div_cancel_left _ (by decide : 0 < 142080),a,H]
    simpa only [queue,records] using entry
  · intro i
    simpa only [← Function.Embedding.trans_apply,← ownerChart] using
      (show B.L (chart i) = S.L (chart i) ∧ B.R (chart i) = S.R (chart i) from
        ⟨(stay _).1.trans (live i).1,(stay _).2.trans (live i).2⟩)
  · intro i programs label child v G d installed localRun otherOwners
    obtain ⟨v',J,called,_,user',view,externalFrame⟩ := exec_emb full.injective installed localRun y rfl B rfl
    have ownerView (l : Fin k) : J.L (lift (owners l)) = G.L ((l.natAdd (s+5)).castAdd back) ∧
        J.R (lift (owners l)) = G.R ((l.natAdd (s+5)).castAdd back) := by
      have eq := congrArg (fun Z : Stacks _ prime => (Z.L ((l.natAdd (s+5)).castAdd back), Z.R ((l.natAdd (s+5)).castAdd back))) view
      simpa [embStk,full,place,recursiveEntryPlacement] using Prod.mk.inj eq
    obtain ⟨out,Z,hu,run,left,right,frame⟩ := recursiveChartReturn_exec body ((select.seq load).seq (clearWorkTapes work)) (embProg full label child) privateBank
      (lift (owners i)) (fun j => lift.injective.ne (apart i _).symm) (Exec.seq exec clear) called
      (fun j => reusable (j.castLE reserve)) (by
        intro j off
        induction j using Fin.addCases with
        | left j =>
          apply outside j
          intro l eq
          apply off ((l.castAdd 5).castAdd back)
          change lift (place (((l.castAdd 5).castAdd k).castAdd back)) = _ at eq
          rw [frontTape] at eq
          exact eq
        | right j => exact ⟨(blank j).1.trans (free j).1.symm,(blank j).2.trans (free j).2.symm⟩) (by
        intro j ne off
        by_cases owner : ∃ l, lift (owners l) = j
        · obtain ⟨l,rfl⟩ := owner
          exact ⟨(ownerView l).1.trans (otherOwners l (fun eq => ne (eq ▸ rfl))).1,
            (ownerView l).2.trans (otherOwners l (fun eq => ne (eq ▸ rfl))).2⟩
        · apply externalFrame j
          intro l
          induction l using Fin.addCases with
          | left l =>
            induction l using Fin.addCases with
            | left l =>
              change lift (place ((l.castAdd k).castAdd back)) ≠ j
              rw [frontTape]
              exact off (l.castAdd back)
            | right l =>
              simpa [full,place,recursiveEntryPlacement] using
                (show lift (owners l) ≠ j from fun eq => owner ⟨l,eq⟩)
          | right l =>
            simpa [full,place,recursiveEntryPlacement,privateBank] using off (l.natAdd (s+5)))
    refine ⟨out,Z,_,hu.trans user',run,left.trans (ownerView i).1,right.trans (ownerView i).2,?_,frame⟩
    unfold chartReturnCost
    simp only [← List.ofFn_eq_map]
    rw [List.ofFn_add,List.map_append,List.sum_append]
    simp only [List.map_ofFn]
    apply congrArg (·+1)
    apply congrArg₂ (·+·) <;> apply congrArg List.sum <;> apply congrArg List.ofFn <;> funext j <;>
      simp [Function.comp_def,privateBank,← view,embStk,full,place,recursiveEntryPlacement]
    rfl

end IntegerMultBounds.MathlibTM2.M6.BitNode
