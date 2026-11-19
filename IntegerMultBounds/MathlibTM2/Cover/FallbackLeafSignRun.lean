module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafFrame
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafNegation
public import IntegerMultBounds.MathlibTM2.Cover.FallbackNegationDimensions

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {F U : Type}

noncomputable def leafSignSetup : Pr F 17 217 prime U :=
  let tail := (bcopy 12 7 1 2).seq (.seq (.act (clearLowBit 7)) (Routing.binaryCanonicalProgram 7 1))
  let product := (bmul 7 4 5 1 2 3 6 9 11).seq (Routing.binaryCanonicalProgram 5 1)
  ((middleRowDescriptor negationSuffixPorts).seq (tail.seq product)).seq ((bcopy 4 10 1 2).seq (bcopy 8 14 1 2))

noncomputable def leafSignReturn : Pr Empty 15 217 prime U :=
  let child : Pr Empty 9 207 prime U := .seq (.act (pushMarkers [3,4,5,6,7,8]))
    (foreign (Alphabet.program RadixToBinary.binaryEncoding (CountedLoop.program BlockNegationReuse.program)))
  let sign := statePlacedNormalized (Fin.castAddEmb 6) (by decide : 207 ≤ 217) (by decide) Empty.elim child
  .seq (.act (pushMarkers ((List.finRange 6).map (Fin.natAddEmb 9)))) (sign.seq (returnWord negationReturnPorts))

def leafSignCost (P G M B : ℕ) : ℕ :=
  let suffix := G*(M*B)
  let count := M-1
  let L := count.size+suffix.size
  let setup := 432*suffix+((6*M.size+6)+(1+(4*M.size+6))+
    (count.size*(12*L+20)+16*L+24+(4*L+6)))+(6*suffix.size+6+(6*P.size+6))
  setup+(2+(1+(P*(210*(M*suffix)+219)+6*P+2*P.size+2)*14+6)+((327*(P*(M*suffix))+2)*13+6))

theorem leafSignRun_exec (body : F → Pr F 17 217 prime U) (P G M B : ℕ)
    (hp : 0 < P) (hg : 0 < G) (hm : 0 < M) (hb : 0 < B) (odd : Odd M)
    (word : Fin (P*(M*(G*(M*B)))) → ZMod 2) (u : HS 17 217 prime U) (S : Stacks 17 prime)
    (payload : ∀ x, readAt blank (S.L 0) (S.R 0) x = leafBitTape (List.ofFn word) x)
    (prefixCount : S.R 8 = binSyms P.size P) (gap : S.R 15 = binSyms G.size G)
    (radix : S.R 12 = binSyms M.size M) (width : S.R 16 = binSyms B.size B)
    (left : ∀ i : Fin 17, i ≠ 0 → i < 15 → S.L i = [])
    (free : ∀ i : Fin 17, i ∈ [1,2,3,4,5,6,7,9,10,11,13,14] → S.R i = []) :
    ∃ z D n, z.user = u.user ∧ n ≤ leafSignCost P G M B ∧
      Exec body (leafSignSetup.seq (embProg (Fin.castAddEmb 2) Empty.elim leafSignReturn)) (mk u S) n (mk z D) ∧
      ∀ x, readAt blank (D.L 0) (D.R 0) x = leafBitTape (negateLeafHead word) x := by
  let suffix := G*(M*B)
  let sym := fun n : ℕ => binSyms (A := prime) n.size n
  let digits := Function.update (Function.update (Function.update
    (Function.update (Function.update S.R 4 (sym suffix)) 7 (sym (M-1))) 5 (sym ((M-1)*suffix)))
    10 (sym suffix)) 14 (sym P)
  let D : Stacks 17 prime := {S with R := digits}
  obtain ⟨v,n,hv,hn,setup⟩ := negationDimensions_exec body P G M B hg hm hb odd u S prefixCount gap radix width
    (fun i hi => free i ((by decide : ∀ j : Fin 17, j ∈ [1,2,3,4,5,6,7,9,10,11,14] →
      j ∈ [1,2,3,4,5,6,7,9,10,11,13,14]) i hi))
  let bank := Fin.castAddEmb (n := 15) 2
  let E := embStk bank D
  have L (i : Fin 15) (hi : i ≠ 0) : E.L i = [] :=
    left (i.castAdd 2) ((Fin.castAddEmb 2).injective.ne hi) i.isLt
  obtain ⟨a,H,m,ha,hm',run,out⟩ := negateAndReturn_exec hp hm (Nat.mul_pos hg (Nat.mul_pos hm hb))
    word (F := Empty) Empty.elim (embDn bank v) E (by
      change ∀ x, readAt blank (S.L 0) (digits 0) x = _
      simpa [digits] using payload)
    (fun i hi => L _ ((Fin.castAddEmb 6).injective.ne hi)) (by
      intro i hi
      fin_cases i
      · contradiction
      · change digits 1 = []
        simp [digits, free 1 (by decide)]
      · change digits 2 = []
        simp [digits, free 2 (by decide)]
      · change digits 3 = []
        simp [digits, free 3 (by decide)]
      · change digits 4 = sym suffix
        simp [digits]
      · change digits 5 = sym ((M-1)*suffix)
        simp [digits]
      · change digits 6 = []
        simp [digits, free 6 (by decide)]
      · change digits 7 = sym (M-1)
        simp [digits]
      · change digits 8 = sym P
        simpa [digits,sym] using prefixCount)
    (fun i => L _ ((by decide : ∀ j : Fin 6, j.natAdd 9 ≠ 0) i)) (by
      intro i
      fin_cases i
      · change digits 9 = []
        simp [digits, free 9 (by decide)]
      · change digits 10 = sym suffix
        simp [digits]
      · change digits 11 = []
        simp [digits, free 11 (by decide)]
      · change digits 12 = sym M
        simpa [digits,sym] using radix
      · change digits 13 = []
        simp [digits, free 13 (by decide)]
      · change digits 14 = sym P
        simp [digits])
  obtain ⟨z,J,placed,_,hz,eq,_⟩ := exec_emb (body' := body) (ι := Empty.elim) bank.injective
    (fun e => nomatch e) run v rfl D rfl
  rw [← eq] at out
  exact ⟨z,J,n+m,hz.trans (ha.trans hv),Nat.add_le_add hn hm',Exec.seq setup placed,out⟩

def signWork : Fin 17 ↪ Fin 31 := Fin.castLEEmb (by decide)

/-- Use the released shear workspace, with the payload at the same caller slot. -/
theorem placedLeafSign_exec {K Q P G M B : ℕ} (slot : Fin K) (capacity : 217 ≤ Q)
    (hp : 0 < P) (hg : 0 < G) (hm : 0 < M) (hb : 0 < B) (odd : Odd M)
    (word : Fin (P*(M*(G*(M*B)))) → ZMod 2)
    (body : F → Pr F (K+31) Q prime U) (u : HS (K+31) Q prime U) (S : Stacks (K+31) prime)
    (payload : ∀ x, readAt blank (S.L (slot.castAdd 31)) (S.R (slot.castAdd 31)) x = leafBitTape (List.ofFn word) x)
    (headers : ∀ i : Fin 17, i ≠ 0 → S.R ((signWork i).natAdd K) =
      if i = 8 then binSyms P.size P else if i = 12 then binSyms M.size M else
      if i = 15 then binSyms G.size G else if i = 16 then binSyms B.size B else [])
    (left : ∀ i : Fin 17, i ≠ 0 → S.L ((signWork i).natAdd K) = []) :
    let bank := signWork.trans (Record.payloadBank slot (0 : Fin 31))
    let child := (leafSignSetup (F := Empty)).seq (embProg (Fin.castAddEmb 2) Empty.elim leafSignReturn)
    ∃ z D n, z.user = u.user ∧ n ≤ 1+leafSignCost P G M B ∧
      Exec body (statePlacedNormalized bank capacity (by decide) Empty.elim child) (mk u S) n (mk z D) ∧
      (∀ x, readAt blank (D.L (slot.castAdd 31)) (D.R (slot.castAdd 31)) x = leafBitTape (negateLeafHead word) x) ∧
      ∀ j : Fin K, j ≠ slot → D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31) := by
  intro bank child
  let E := embStk bank S
  have shared : bank 0 = slot.castAdd 31 := Record.payloadBank_shared slot 0
  have inside (i : Fin 17) (hi : i ≠ 0) : bank i = (signWork i).natAdd K :=
    Record.payloadBank_private slot 0 _ (signWork.injective.ne hi)
  have right (i : Fin 17) (hi : i ≠ 0) := headers i hi
  have entry (i : Fin 17) (hi : i ≠ 0) : E.R i =
      (if i = 8 then binSyms P.size P else if i = 12 then binSyms M.size M else
      if i = 15 then binSyms G.size G else if i = 16 then binSyms B.size B else []) := by
    change S.R (bank i) = _
    rw [inside i hi]; exact right i hi
  obtain ⟨a,H,n,ha,hn,run,out⟩ := leafSignRun_exec (F := Empty) Empty.elim P G M B hp hg hm hb odd word
    (stateLiftDown (by decide : 0 < 217) (embDn bank u)) E (by
      change ∀ x, readAt blank (S.L (bank 0)) (S.R (bank 0)) x = _
      rwa [shared]) (by simpa using entry 8 (by decide)) (by simpa using entry 15 (by decide))
    (by simpa using entry 12 (by decide)) (by simpa using entry 16 (by decide))
    (by intro i hi _; change S.L (bank i) = []; rw [inside i hi]; exact left i hi) (by
      intro i hi
      have h := (by decide : ∀ j : Fin 17, j ∈ [1,2,3,4,5,6,7,9,10,11,13,14] →
        j ≠ 0 ∧ j ≠ 8 ∧ j ≠ 12 ∧ j ≠ 15 ∧ j ≠ 16) i hi
      simpa [h] using entry i h.1)
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized bank bank.injective capacity (by decide)
    Empty.elim (body' := body) (fun e => nomatch e) u S run
  let D := embOvr bank H.get S
  have eq : embStk bank D = H := embStk_ovr bank.injective _ _
  rw [← eq] at out
  change ∀ x, readAt blank (D.L (bank 0)) (D.R (bank 0)) x = _ at out
  rw [shared] at out
  refine ⟨z,D,_,hz.trans ha,Nat.add_le_add_left hn 1,placed,out,?_⟩
  intro j hj
  apply embOvr_off
  intro i
  by_cases hi : i = 0
  · subst i; rw [shared]; exact (Fin.castAddEmb 31).injective.ne hj.symm
  · rw [inside i hi]
    intro hit
    have h := congrArg Fin.val hit
    simp only [Fin.val_natAdd,Fin.val_castAdd] at h
    omega

def signHeaderTargets : Fin 4 ↪ Fin 31 := ⟨![8,15,12,16],by decide⟩

theorem loadedLeafSign_exec {K Q P G M B : ℕ} (slot : Fin K) (capacity : 217 ≤ Q)
    (hp : 0 < P) (hg : 0 < G) (hm : 0 < M) (hb : 0 < B) (odd : Odd M)
    (word : Fin (P*(M*(G*(M*B)))) → ZMod 2) (src : Fin 4 → Fin K)
    (body : F → Pr F (K+31) Q prime U) (u : HS (K+31) Q prime U) (S : Stacks (K+31) prime)
    (payload : ∀ x, readAt blank (S.L (slot.castAdd 31)) (S.R (slot.castAdd 31)) x = leafBitTape (List.ofFn word) x)
    (headers : ∀ i, S.R ((src i).castAdd 31) =
      (![binSyms P.size P,binSyms G.size G,binSyms M.size M,binSyms B.size B] i))
    (free : ∀ i : Fin 31, S.L (i.natAdd K) = [] ∧ S.R (i.natAdd K) = []) :
    let fromTape := fun i => (src i).castAdd 31
    let targets := signHeaderTargets.trans (Fin.natAddEmb K)
    let setup := Record.copyLeafHeaders fromTape targets ((1 : Fin 31).natAdd K) ((2 : Fin 31).natAdd K) (List.finRange 4)
    let bank := signWork.trans (Record.payloadBank slot (0 : Fin 31))
    let child := (leafSignSetup (F := Empty)).seq (embProg (Fin.castAddEmb 2) Empty.elim leafSignReturn)
    ∃ z D n, z.user = u.user ∧ n ≤ (6*(P.size+G.size+M.size+B.size)+25)+(1+leafSignCost P G M B) ∧
      Exec body (setup.seq (statePlacedNormalized bank capacity (by decide) Empty.elim child)) (mk u S) n (mk z D) ∧
      (∀ x, readAt blank (D.L (slot.castAdd 31)) (D.R (slot.castAdd 31)) x = leafBitTape (negateLeafHead word) x) ∧
      ∀ j : Fin K, j ≠ slot → D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31) := by
  intro fromTape targets setup bank child
  have apart (i : Fin K) (j : Fin 31) : i.castAdd 31 ≠ j.natAdd K := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  have distinct (i : Fin 4) : [fromTape i,targets i,(1 : Fin 31).natAdd K,(2 : Fin 31).natAdd K].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.Nodup.map (Fin.natAddEmb K).injective ((by decide : ∀ j, [signHeaderTargets j,1,2].Nodup) i)⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨apart _ _,apart _ _,apart _ _⟩
  obtain ⟨v,H,hv,copy,left,loaded,off⟩ := Record.copyLeafHeaders_exec body fromTape targets _ _
    (fun i j => apart _ _) distinct (List.finRange 4) (List.nodup_finRange _) u S (free 1).2 (free 2).2
    (fun i _ => (free _).2)
  have keep (j : Fin K) := off (j.castAdd 31) (fun i _ => (apart j (signHeaderTargets i)).symm)
  have get (i : Fin 4) := (loaded i (List.mem_finRange i)).trans (headers i)
  obtain ⟨z,D,n,hz,hn,run,out,frame⟩ := placedLeafSign_exec slot capacity hp hg hm hb odd word body v H
    (by rw [left,keep]; exact payload) (by
      intro i hi
      by_cases h8 : i = 8
      · subst i; simpa [targets,signHeaderTargets,signWork,Fin.natAddEmb_apply] using get 0
      by_cases h12 : i = 12
      · subst i; simpa [targets,signHeaderTargets,signWork,Fin.natAddEmb_apply] using get 2
      by_cases h15 : i = 15
      · subst i; simpa [targets,signHeaderTargets,signWork,Fin.natAddEmb_apply] using get 1
      by_cases h16 : i = 16
      · subst i; simpa [targets,signHeaderTargets,signWork,Fin.natAddEmb_apply] using get 3
      simp only [ite_eq_right h8,ite_eq_right h12,ite_eq_right h15,ite_eq_right h16]
      apply Eq.trans (off _ _) (free _).2
      intro j _
      apply (Fin.natAddEmb K).injective.ne
      exact (by decide : ∀ (k : Fin 17), k ≠ 8 → k ≠ 12 → k ≠ 15 → k ≠ 16 →
        ∀ j, signHeaderTargets j ≠ signWork k) i h8 h12 h15 h16 j)
    (fun i _ => left ▸ (free _).1)
  have cost : ((List.finRange 4).map fun i => 6*(S.R (fromTape i)).length+6).sum+1 =
      6*(P.size+G.size+M.size+B.size)+25 := by
    change (6*(S.R (fromTape 0)).length+6 + (6*(S.R (fromTape 1)).length+6 +
      (6*(S.R (fromTape 2)).length+6 + (6*(S.R (fromTape 3)).length+6 + 0))))+1 = _
    simp only [fromTape,headers]
    change 6*(binSyms (A := prime) P.size P).length+6 + _ + 1 = _
    simp [length_binSyms]; ring
  rw [cost] at copy
  refine ⟨z,D,_,hz.trans hv,Nat.add_le_add_left hn _,Exec.seq copy run,out,?_⟩
  intro j hj
  exact ⟨(frame j hj).1.trans (congrFun left _),(frame j hj).2.trans (keep j)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
