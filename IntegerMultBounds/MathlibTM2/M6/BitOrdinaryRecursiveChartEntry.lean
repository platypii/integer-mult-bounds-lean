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

/-- Install the child chart in the caller with a fixed splitter placement.
The nine sources and cutoff are the actual replay ports. -/
theorem recursiveRoleChartEntry_exec {n K T Q s k back w : ℕ} {P U : Type}
    (room : 16 ≤ T) (replay : Fin (66+(K+3+T)) ↪ Fin n)
    (place : Fin (((s+5)+k)+back) ↪ Fin n) (space : 59 ≤ s)
    (separate : ∀ i j, replay i ≠ place j)
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
    (∀ j : Fin (s+5), let i := full ((j.castAdd k).castAdd back); S.L i = [] ∧ S.R i = []) →
    (∀ j : Fin back, let i := full (j.natAdd ((s+5)+k)); S.L i = [] ∧ S.R i = []) →
    ∀ c, Fast.Main.mnProgPush (select.seq load) ≤ c → (∀ f, Fast.Main.mnProgPush (body f) ≤ c) →
    let budget := (149*(roleSplitTapes+5)+2417)*(a*rows*142080*H*V)
    ∃ z F t, z.user = u.user ∧ t ≤ budget+roleSplitWorkspace*(6*(c*budget)+4)+1 ∧
      Exec body ((select.seq load).seq (clearWorkTapes work)) (mk u S) t (mk z F) ∧
      ordinaryParentEntry (T := s) back (directoryChartWords (S.R cut) W a rows H true weights width queue)
        (embStk chart F) = embStk full F ∧
      (∀ i, F.L (chart i) = S.L (chart i) ∧ F.R (chart i) = S.R (chart i)) ∧
      (∀ j : Fin n, (∀ i, scanner i ≠ lift j) → F.L (lift j) = S.L (lift j) ∧ F.R (lift j) = S.R (lift j)) ∧
      ∀ i : Fin roleSplitWorkspace, F.L (i.natAdd n) = [] ∧ F.R (i.natAdd n) = [] := by
  intro W a H lift full split sources cut scratch select localBank scanner chart dst port source load work V weights queue cutFits headers free front suffix c push bodies budget
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
  have dstLow (i) : dst i = lift (place (localBank (((ordinaryMetadataPorts i).castLE space)))) := rfl
  have srcDst (i j) : source i ≠ dst j := by
    rw [dstLow]
    by_cases eq : i = 8
    · subst i; exact (show source 8 = _ from Function.update_self ..) ▸ disjoint (port.castAdd 12) _
    · rw [show source i = sources i from Function.update_of_ne eq ..]
      exact lift.injective.ne (separate _ _)
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
    srcDst ports (fun i => lift.injective.ne (separate _ _)) (by
      change [cut,scanner ((40 : Fin 59).castLE space),scratch 0,scratch 1].Nodup
      have sep : cut ≠ scanner ((40 : Fin 59).castLE space) := lift.injective.ne (separate _ _)
      simp [sep,scratchNe,show ∀ i, cut ≠ scratch i from fun i => (disjoint _ _).symm,
        show ∀ i, scanner ((40 : Fin 59).castLE space) ≠ scratch i from fun i => (disjoint _ _).symm])
    (free _).2 (free _).2 front suffix h₀ h₁ h₂ h₃ (fun i hi => (privateCount i hi).symm ▸ (free _).2)
    (fun j => (high j).symm ▸ (free _).1) (fun j => (high j).symm ▸ (free _).2)
  obtain ⟨y,B,m,same,time,clear,base,blank⟩ := releaseSplitWorkspace_exec body (select.seq load) u z S F t c exec push bodies free
  have stay (i : Fin n) : B.L (lift i) = F.L (lift i) ∧ B.R (lift i) = F.R (lift i) :=
    ⟨congrArg (fun Z : Stacks n prime => Z.L i) base,congrArg (fun Z : Stacks n prime => Z.R i) base⟩
  have projected {l : ℕ} (e : Fin l ↪ Fin n) : embStk (e.trans lift) B = embStk (e.trans lift) F :=
    congrArg (embStk e) base
  refine ⟨y,B,t+m,same.trans user,?_,Exec.seq exec clear,?_,?_,?_,blank⟩
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
    exact ⟨(stay _).1.trans (live i).1,(stay _).2.trans (live i).2⟩
  · intro j off
    have kept := frame _ (fun i => (high i).symm ▸ disjoint _ j) off
    exact ⟨(stay j).1.trans kept.1,(stay j).2.trans kept.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
