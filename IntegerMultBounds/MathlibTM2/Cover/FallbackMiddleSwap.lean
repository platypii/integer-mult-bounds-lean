module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackMiddleReturn
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafFrame

/-! Place the middle shear beside the leaf interchange with one common payload tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout SharedBankStageInput
variable {T P M G B : ℕ} {F U : Type}

/-- Prefix, gap, coefficient, initial digit, block width and modulus. -/
def middleHeaderTargets : Fin 6 ↪ Fin 31 := ⟨![28,29,0,1,18,20],by decide⟩

theorem copyMiddleHeaders_exec {n Q A : ℕ} (body : F → Pr F (n+31) Q A U) (src : Fin 6 → Fin n)
    (v : HS (n+31) Q A U) (S : Stacks (n+31) A)
    (free : ∀ j : Fin 31, S.R (j.natAdd n) = []) :
    let fromTape := fun i => (src i).castAdd 31
    let targets := middleHeaderTargets.trans (Fin.natAddEmb n)
    let ticks := ((List.finRange 6).map fun i => 6*(S.R (fromTape i)).length+6).sum+1
    ∃ z D, z.user = v.user ∧
      Exec body (Record.copyLeafHeaders fromTape targets ((4 : Fin 31).natAdd n) ((5 : Fin 31).natAdd n) (List.finRange 6))
        (mk v S) ticks (mk z D) ∧ D.L = S.L ∧
      (∀ i, D.R (targets i) = S.R (fromTape i)) ∧
      (∀ j : Fin n, D.R (j.castAdd 31) = S.R (j.castAdd 31)) ∧
      ∀ j : Fin 31, (∀ i, middleHeaderTargets i ≠ j) → D.R (j.natAdd n) = [] := by
  intro fromTape targets ticks
  have apart (i : Fin n) (j : Fin 31) : i.castAdd 31 ≠ j.natAdd n := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  have ports (i : Fin 6) : [fromTape i,targets i,(4 : Fin 31).natAdd n,(5 : Fin 31).natAdd n].Nodup := by
    have distinct : [middleHeaderTargets i,(4 : Fin 31),5].Nodup := (by decide : ∀ j, [middleHeaderTargets j,(4 : Fin 31),5].Nodup) i
    apply List.nodup_cons.mpr
    refine ⟨?_,distinct.map (Fin.natAddEmb n).injective⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨apart _ _,apart _ _,apart _ _⟩
  obtain ⟨z,D,hz,run,left,loaded,off⟩ := Record.copyLeafHeaders_exec body fromTape targets _ _
    (fun i j => apart _ _) ports (List.finRange 6) (List.nodup_finRange _) v S (free 4) (free 5)
    (fun i _ => free _)
  exact ⟨z,D,hz,run,left,fun i => loaded i (List.mem_finRange i),
    fun j => off _ (fun i _ => (apart j (middleHeaderTargets i)).symm),
    fun j hj => (off _ (fun i _ => (Fin.natAddEmb n).injective.ne (hj i))).trans (free j)⟩

noncomputable def initializedMiddleShear : Pr Empty 31 217 prime U :=
  .seq (bcopy 20 2 4 5) (.seq (.act (.push (.lt 30) (fun _ => separator) .done)) (.seq (initializeBank (middleTranslation.trans middleWork))
    (returnedMiddleShear (Function.Embedding.refl _))))

/-- A shear on a shared role returns its bit word in place and preserves
both stacks of every other caller tape. -/
theorem placedMiddleShear_exec {K Q : ℕ} (slot : Fin K) (capacity : 217 ≤ Q)
    (w c : ℕ) (radix : M = prime^(w+1)) (hc : c < M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (word : Fin ((P*M*G)*(M*B)) → ZMod 2) :
    let bank := Record.payloadBank slot (22 : Fin 31)
    let shear := statePlacedNormalized bank capacity (by decide : 0 < 217) Empty.elim initializedMiddleShear
    ∀ (body : F → Pr F (K+31) Q prime U) (u : HS (K+31) Q prime U) (S : Stacks (K+31) prime),
        let E := embStk bank S
        E.R 28 = binSyms P.size P → E.R 29 = binSyms G.size G →
          (∀ i : Fin 30, 24 ≤ i → i ≤ 27 → E.R (middleWork i) = []) →
          E.R 0 = binSyms M.size c → E.R 1 = binSyms M.size 0 → E.R 2 = [] →
          (∀ i : Fin 13, 3 ≤ i → i < 12 → E.R (middleWork (middleArithmetic i)) = []) →
          E.L 30 = [] → E.R 30 = [] →
          (∀ i : Fin 12, i < 10 → E.L (middleWork (middleTranslation i)) = []) →
          (∀ i : Fin 12, i < 10 → E.R (middleWork (middleTranslation i)) =
            if i = 5 then binSyms B.size B else if i = 7 then binSyms M.size M else []) →
          E.L 23 = [] → E.R 23 = [] →
          (∀ x, readAt blank (S.L (slot.castAdd 31)) (S.R (slot.castAdd 31)) x = leafBitTape (List.ofFn word) x) →
          ∃ z D n, z.user = u.user ∧ n ≤ (6*M.size+9)+(210*(2*(Nat.size prime+1)^2)+16120)*((P*M*G)*(M*B)) ∧
            Exec body shear (mk u S) n (mk z D) ∧
            (∀ x, readAt blank (D.L (slot.castAdd 31)) (D.R (slot.castAdd 31)) x =
              leafBitTape (FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)) x) ∧
            ∀ j : Fin K, j ≠ slot → D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31) := by
  intro bank shear body u S E heads ticks free coef digit modulus scratch marker fresh left right dl dr input
  let bs := binBits B.size B
  let ms := binBits M.size M
  have hb := Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self B)
  have hm := Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self M)
  have cb := Mult.PhaseCellToeplitz.binBits_size_canonical B
  have cm := Mult.PhaseCellToeplitz.binBits_size_canonical M
  have shared : bank 22 = slot.castAdd 31 := Record.payloadBank_shared slot 22
  have src (x : ℤ) : RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ word)) x) =
      readAt blank (E.L 22) (E.R 22) x := by
    change _ = readAt blank (S.L (bank 22)) (S.R (bank 22)) x
    rw [shared]
    simpa only [leafBitTape,List.map_ofFn] using (input x).symm
  let u₀ := stateLiftDown (by decide : 0 < 217) (embDn bank u)
  have modHeader : E.R 20 = binSyms M.size M := by change E.R (middleWork (middleTranslation 7)) = _; simpa using right 7 (by decide)
  obtain ⟨u₁,hcopy,copy⟩ := bcopy_exec (body := (Empty.elim : Empty → Pr Empty 31 217 prime U))
    (a := 20) (c := 2) (t₁ := 4) (t₂ := 5) (by decide) u₀ E
    (scratch 4 (by decide) (by decide)) (scratch 5 (by decide) (by decide))
  rw [modHeader,modulus,List.append_nil,length_binSyms] at copy
  let C : Stacks 31 prime := {E with R := Function.update E.R 2 (binSyms M.size M)}
  have sameR (j : Fin 31) (hj : j ≠ 2) : C.R j = E.R j := Function.update_of_ne hj _ _
  let markedE : Stacks 31 prime := {C with L := Function.update E.L 30 [separator]}
  have mark := Exec.act (body := (Empty.elim : Empty → Pr Empty 31 217 prime U))
    (.push (.lt 30) (fun _ => separator) .done) (mk u₁ C)
  have install : Exec Empty.elim (.act (.push (.lt 30) (fun _ => separator) .done))
      (mk u₁ C) 1 (mk u₁ markedE) := by
    simpa [markedE,Action.run,update_lt,store_mk,C,marker] using mark
  have untouched (i : Fin 12) : markedE.L (middleWork (middleTranslation i)) =
      E.L (middleWork (middleTranslation i)) :=
    Function.update_of_ne ((by decide : ∀ j, middleWork (middleTranslation j) ≠ 30) i) _ _
  obtain ⟨I,init,rs,marked,keep,rep⟩ := initializeBank_exec (P := Empty) Empty.elim
    (middleTranslation.trans middleWork) bs ms
    (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ word))) (fun _ => blank) 0 0
    u₁ markedE (fun i hi => (untouched i).trans (left i hi))
    (fun i hi => by rw [show markedE.R ((middleTranslation.trans middleWork) i) = E.R (middleWork (middleTranslation i)) from sameR _ ((by decide : ∀ j, middleWork (middleTranslation j) ≠ 2) i)]; simpa only [bs,ms,binSyms_eq,markedE,Function.Embedding.trans_apply] using right i hi)
    (by intro x; rw [sub_zero]; change _ = readAt blank (markedE.L (middleWork (middleTranslation 10))) (C.R 22) x; rw [untouched,sameR _ (by decide)]; exact src x) (by
      intro x
      change blank = readAt blank (markedE.L 23) (C.R 23) (x-0)
      simp [markedE,C,Function.update_of_ne,dl,dr,readAt_nil_left,wordTape_nil])
  have ready : MiddleGroupReady middleArithmetic M.size c 0 M (embStk middleWork I) :=
    by
    change I.R 0 = _ ∧ I.R 1 = _ ∧ I.R 2 = _ ∧ (∀ i : Fin 13, 3 ≤ i → i < 12 →
      I.R (middleWork (middleArithmetic i)) = []) ∧ I.L 3 = _
    rw [rs]
    refine ⟨(sameR 0 (by decide)).trans coef,(sameR 1 (by decide)).trans digit,by simp [markedE,C],?_,marked⟩
    intro i lo hi
    apply Eq.trans (sameR _ _) (scratch i lo hi)
    intro eq
    have h := congrArg Fin.val eq
    change i.val = 2 at h
    omega
  obtain ⟨a,D,n,ha,hn,run,payload,_⟩ := returnedMiddleShear_exec (F := Empty) Empty.elim (Function.Embedding.refl _)
    w c radix hc hP hG hB (fun _ => blank) (fun _ => blank) 0 0 (SparseRoleCircuit.encode ∘ word)
    bs ms hb hm cb cm u₁ I (rs ▸ (sameR 28 (by decide)).trans heads) (rs ▸ (sameR 29 (by decide)).trans ticks)
    (by intro i lo hi; rw [rs]; apply Eq.trans (sameR _ _) (free i lo hi)
        intro eq; have h := congrArg Fin.val eq; change i.val = 2 at h; omega) ready
    ((keep 30 (by decide)).trans (by simp [markedE])) (rs ▸ (sameR 30 (by decide)).trans fresh) rep (fun _ _ _ => rfl)
  obtain ⟨b,H,hb',placed,eq,frame⟩ := Record.payloadFrame_exec capacity slot (22 : Fin 31) (by decide)
    body initializedMiddleShear u S a D ((6*M.size+6)+(1+(1+n))) (Exec.seq copy (Exec.seq install (Exec.seq init run)))

  have read := payload
  rw [← eq] at read
  change ∀ x, readAt blank (H.L (bank 22)) (H.R (bank 22)) (x-0) = _ at read
  rw [shared] at read
  refine ⟨b,H,_,hb'.trans (ha.trans hcopy),?_,placed,?_,frame⟩
  · rw [show 1+((6*M.size+6)+(1+(1+n))) = (6*M.size+9)+n by omega]
    exact Nat.add_le_add_left hn _
  · simpa only [leafBitTape,translated_map,sub_zero] using read

theorem middleSwap_exec [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (size : (P*M*G)*(M*B) = volume prime v) (w c : ℕ) (radix : M = prime^(w+1))
    (hc : c < M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (word : Fin ((P*M*G)*(M*B)) → ZMod 2) (io : Fin T) (roles : Tapes T prime)
    (head : roles.head io = 0) (input : roles.tape io = leafBitTape (List.ofFn word))
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let block := LeafCore.core io
    ∀ {K : ℕ} (sim : Fin block.tapes ↪ Fin K),
    let ports := sim.trans (Fin.castAddEmb 31)
    ∀ (slot : Fin block.tapes) (capacity : 217 ≤ block.states), slot.val = io.val →
      let bank := Record.payloadBank (sim slot) (22 : Fin 31)
      let shear := statePlacedNormalized bank capacity (by decide : 0 < 217) Empty.elim
        initializedMiddleShear
      let N := (P*M*G)*(M*B)
      let xs := FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)
      let y := swapLeafList v size xs (FiberLayoutData.translated_length ..)
      ∀ (body : F → Pr F (K+31) block.states prime U)
        (u : HS (K+31) block.states prime U) (S : Stacks (K+31) prime),
        let E := embStk bank S
        E.R 28 = binSyms P.size P → E.R 29 = binSyms G.size G →
          (∀ i : Fin 30, 24 ≤ i → i ≤ 27 → E.R (middleWork i) = []) →
          E.R 0 = binSyms M.size c → E.R 1 = binSyms M.size 0 → E.R 2 = [] →
          (∀ i : Fin 13, 3 ≤ i → i < 12 → E.R (middleWork (middleArithmetic i)) = []) →
          E.L 30 = [] → E.R 30 = [] →
          (∀ i : Fin 12, i < 10 → E.L (middleWork (middleTranslation i)) = []) →
          (∀ i : Fin 12, i < 10 → E.R (middleWork (middleTranslation i)) =
            if i = 5 then binSyms B.size B else if i = 7 then binSyms M.size M else []) →
          E.L 23 = [] → E.R 23 = [] →
          RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
          ∃ z D n, z.user = u.user ∧
            n ≤ (6*M.size+9)+(210*(2*(Nat.size prime+1)^2)+16120)*N+(LeafCore.coreCost (volume prime v) v.width*(block.tapes+5)+6) ∧
            Exec body (.seq shear (embProg ports Empty.elim (foreign block.program))) (mk u S) n (mk z D) ∧
            RepT (raw (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn y)) 0)
              (Routines.hdr v) f p node scalar ctr st) block.tapes) (D.L ∘ ports) (D.R ∘ ports) ∧
            (∀ x, readAt blank (D.L (ports slot)) (D.R (ports slot)) x = leafBitTape (List.ofFn y) x) ∧
            ∀ j : Fin K, (∀ i, sim i ≠ j) →
              D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31) := by
  intro block K sim ports slot capacity leading bank shear N xs y body u S E heads ticks free coef digit modulus scratch marker fresh left right dl dr initial
  have cell := initial slot
  have inside : slot.val < CommonBank.count T := leading ▸ (LeafCore.roleSlot io).isLt
  have same : (⟨slot.val,inside⟩ : Fin (CommonBank.count T)) = LeafCore.roleSlot io := Fin.ext leading
  obtain ⟨hh,ht⟩ := LeafCore.bank_role roles (Routines.hdr v) f p node scalar ctr st io
  obtain ⟨b,H,n,hu,hn,placed,read,frame⟩ := placedMiddleShear_exec (sim slot) capacity w c radix hc hP hG hB
    word body u S heads ticks free coef digit modulus scratch marker fresh left right dl dr (by
      intro x
      simpa only [ports,Function.Embedding.trans_apply,Fin.castAddEmb_apply,raw,dite_eq_left inside,same,hh,ht,head,input,sub_zero,Function.comp_apply] using (cell x).symm)
  obtain ⟨z,J,k,hz,hk,exec,result,out,unchanged⟩ := swapReturnedShear_exec v positive size word
    (fun i => c*(i.val/G%M)%M) io roles f p node scalar ctr st ports body shear u b S H slot n
    leading initial placed hu (fun i hi => frame (sim i) (sim.injective.ne hi)) (by simpa only [ports,Function.Embedding.trans_apply,Fin.castAddEmb_apply,leafBitTape,translated_map] using read)
  have bound := Nat.add_le_add_right hn (LeafCore.coreCost (volume prime v) v.width*(block.tapes+5)+6)
  refine ⟨z,J,k,hz,hk.trans bound,exec,result,out,?_⟩
  intro j off
  have untouched := unchanged (j.castAdd 31) (fun i => (Fin.castAddEmb 31).injective.ne (off i))
  have kept := frame j (off slot).symm
  exact ⟨untouched.1.trans kept.1,untouched.2.trans kept.2⟩

theorem releaseMiddleWork {k Q A : ℕ} (body : F → Pr F (k+31) Q A U)
    (prog : Pr F (k+31) Q A U) {u z : HS (k+31) Q A U} {S D : Stacks (k+31) A}
    {steps budget push : ℕ} (completed : Exec body prog (mk u S) steps (mk z D)) (time : steps ≤ budget)
    (hp : Fast.Main.mnProgPush prog ≤ push) (hbody : ∀ f, Fast.Main.mnProgPush (body f) ≤ push)
    (free : ∀ j : Fin 31, S.L (j.natAdd k) = [] ∧ S.R (j.natAdd k) = []) :
    let work := (List.finRange 31).map (Fin.natAddEmb k)
    ∃ y E n, y.user = z.user ∧ n ≤ budget+(125+31*(6*(push*budget))) ∧
      Exec body (prog.seq (clearWorkTapes work)) (mk u S) n (mk y E) ∧
      (∀ i : Fin k, E.L (i.castAdd 31) = D.L (i.castAdd 31) ∧ E.R (i.castAdd 31) = D.R (i.castAdd 31)) ∧
      ∀ j : Fin 31, E.L (j.natAdd k) = [] ∧ E.R (j.natAdd k) = [] := by
  intro work
  obtain ⟨z',user,clear⟩ := clearWorkTapes_exec body work
    ((List.nodup_finRange 31).map (Fin.natAddEmb k).injective) z D
  have charge := cleanup_cost_le work completed hp hbody
  have base : (work.map fun j => 4*(S.L j).length+2*(S.R j).length+4).sum = 124 := by
    have eq := List.map_congr_left (l := work) (g := fun _ => 4)
      (f := fun j => 4*(S.L j).length+2*(S.R j).length+4) (by
        intro j hj
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
        simp [(free i).1,(free i).2])
    rw [eq,List.map_const',List.sum_replicate_nat]
    simp [work]
  rw [base,show work.length = 31 by simp [work]] at charge
  have off (i : Fin k) : i.castAdd 31 ∉ work := by
    intro hit
    obtain ⟨j,_,eq⟩ := List.mem_map.mp hit
    have impossible := congrArg Fin.val eq
    change k+j.val = i.val at impossible
    omega
  refine ⟨z',_,_,user,Nat.add_le_add time (charge.trans (by gcongr)),Exec.seq completed clear,?_,?_⟩
  · intro i
    simp [off i]
  · intro j
    have hit : j.natAdd k ∈ work := List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩
    simp [hit]

private theorem middleHeaderCost {k : ℕ} (S : Stacks k prime) (fromTape : Fin 6 → Fin k)
    (headers : ∀ i, S.R (fromTape i) = (![binSyms P.size P,binSyms G.size G,binSyms M.size c,
      binSyms M.size 0,binSyms B.size B,binSyms M.size M] i)) : ((List.finRange 6).map fun i => 6*(S.R (fromTape i)).length+6).sum+1 =
      6*(P.size+G.size+3*M.size+B.size)+37 := by
    change (6*(S.R (fromTape 0)).length+6 + (6*(S.R (fromTape 1)).length+6 +
      (6*(S.R (fromTape 2)).length+6 + (6*(S.R (fromTape 3)).length+6 +
      (6*(S.R (fromTape 4)).length+6 + (6*(S.R (fromTape 5)).length+6 + 0))))))+1 = _
    rw [headers 0,headers 1,headers 2,headers 3,headers 4,headers 5]
    change 6*(binSyms (A := prime) P.size P).length+6 + _ + 1 = _
    simp [length_binSyms]
    ring

theorem loadedMiddleSwap_exec [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (size : (P*M*G)*(M*B) = volume prime v) (w c : ℕ) (radix : M = prime^(w+1))
    (hc : c < M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (word : Fin ((P*M*G)*(M*B)) → ZMod 2) (io : Fin T) (roles : Tapes T prime)
    (head : roles.head io = 0) (input : roles.tape io = leafBitTape (List.ofFn word))
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let block := LeafCore.core io
    ∀ {K : ℕ} (sim : Fin block.tapes ↪ Fin K),
    let ports := sim.trans (Fin.castAddEmb 31)
    ∀ (src : Fin 6 → Fin K) (slot : Fin block.tapes) (capacity : 217 ≤ block.states), slot.val = io.val →
      let bank := Record.payloadBank (sim slot) (22 : Fin 31)
      let shear := statePlacedNormalized bank capacity (by decide : 0 < 217) Empty.elim
        initializedMiddleShear
      let N := (P*M*G)*(M*B)
      let xs := FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)
      let y := swapLeafList v size xs (FiberLayoutData.translated_length ..)
      ∀ (body : F → Pr F (K+31) block.states prime U)
        (u : HS (K+31) block.states prime U) (S : Stacks (K+31) prime),
        let fromTape := fun i => (src i).castAdd 31
        let targets := middleHeaderTargets.trans (Fin.natAddEmb K)
        let setup : Pr F (K+31) block.states prime U := Record.copyLeafHeaders fromTape targets ((4 : Fin 31).natAdd K)
          ((5 : Fin 31).natAdd K) (List.finRange 6)
        let prog := setup.seq (.seq shear (embProg ports Empty.elim (foreign block.program)))
        let work := (List.finRange 31).map (Fin.natAddEmb K)
        let budget := (6*(P.size+G.size+3*M.size+B.size)+37)+((6*M.size+9)+
          (210*(2*(Nat.size prime+1)^2)+16120)*N+(LeafCore.coreCost (volume prime v) v.width*(block.tapes+5)+6))
        ∀ push, Fast.Main.mnProgPush prog ≤ push → (∀ f, Fast.Main.mnProgPush (body f) ≤ push) →
        (∀ j : Fin 31, S.L (j.natAdd K) = [] ∧ S.R (j.natAdd K) = []) →
        (∀ i, S.R (fromTape i) = (![binSyms P.size P,binSyms G.size G,binSyms M.size c,
          binSyms M.size 0,binSyms B.size B,binSyms M.size M] i)) →
          RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
          ∃ z D n, z.user = u.user ∧
            n ≤ budget+(125+31*(6*(push*budget))) ∧
            Exec body (prog.seq (clearWorkTapes work)) (mk u S) n (mk z D) ∧
            RepT (raw (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn y)) 0)
              (Routines.hdr v) f p node scalar ctr st) block.tapes) (D.L ∘ ports) (D.R ∘ ports) ∧
            (∀ x, readAt blank (D.L (ports slot)) (D.R (ports slot)) x = leafBitTape (List.ofFn y) x) ∧
            (∀ j : Fin 31, D.L (j.natAdd K) = [] ∧ D.R (j.natAdd K) = []) ∧
            ∀ j : Fin K, (∀ i, sim i ≠ j) →
              D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31) := by
  intro block K sim ports src slot capacity leading bank shear N xs y body u S fromTape targets setup prog work budget push hp hbody free headers initial
  obtain ⟨b,H,hb,copy,left,loaded,caller,unused⟩ := copyMiddleHeaders_exec body src u S (fun j => (free j).2)
  let E := embStk bank H
  have entry (i : Fin 6) : E.R (middleHeaderTargets i) =
      (![binSyms P.size P,binSyms G.size G,binSyms M.size c,binSyms M.size 0,binSyms B.size B,binSyms M.size M] i) :=
    calc E.R (middleHeaderTargets i) = H.R (targets i) := by
           change H.R (bank _) = _
           rw [show bank (middleHeaderTargets i) = (middleHeaderTargets i).natAdd K from
             Record.payloadBank_private (sim slot) 22 _ ((by decide : ∀ j, middleHeaderTargets j ≠ 22) i)]
           rfl
         _ = _ := (loaded i).trans (headers i)
  have right (j : Fin 31) (privateSlot : j ≠ 22) (off : ∀ i, middleHeaderTargets i ≠ j) : E.R j = [] := by
    change H.R (Record.payloadBank (sim slot) 22 j) = []
    rw [Record.payloadBank_private _ _ _ privateSlot]
    exact unused j off
  have blankL (j : Fin 31) (privateSlot : j ≠ 22) : E.L j = [] := by
    change H.L (Record.payloadBank (sim slot) 22 j) = []
    rw [left,Record.payloadBank_private _ _ _ privateSlot]
    exact (free j).1
  obtain ⟨z,D,n,hz,hn,run,rep,out,off⟩ := middleSwap_exec v positive size w c radix hc hP hG hB word io roles
    head input f p node scalar ctr st sim slot capacity leading body b H (entry 0) (entry 1)
    (fun i lo hi => right _ ((by decide : ∀ j : Fin 30, 24 ≤ j → j ≤ 27 → middleWork j ≠ 22) i lo hi)
      ((by decide : ∀ j : Fin 30, 24 ≤ j → j ≤ 27 → ∀ k, middleHeaderTargets k ≠ middleWork j) i lo hi))
    (entry 2) (entry 3) (right 2 (by decide) (by decide))
    (fun i lo hi => right _ ((by decide : ∀ j : Fin 13, middleWork (middleArithmetic j) ≠ 22) i)
      ((by decide : ∀ j : Fin 13, 3 ≤ j → j < 12 → ∀ k, middleHeaderTargets k ≠ middleWork (middleArithmetic j)) i lo hi))
    (blankL 30 (by decide)) (right 30 (by decide) (by decide))
    (fun i hi => blankL _ ((by decide : ∀ j : Fin 12, j < 10 → middleWork (middleTranslation j) ≠ 22) i hi))
    (by intro i hi
        by_cases width : i = 5
        · subst i; exact entry 4
        by_cases modulus : i = 7
        · subst i; exact entry 5
        simp only [ite_eq_right width,ite_eq_right modulus]
        exact right _ ((by decide : ∀ j : Fin 12, j < 10 → middleWork (middleTranslation j) ≠ 22) i hi)
          ((by decide : ∀ j : Fin 12, j < 10 → j ≠ 5 → j ≠ 7 → ∀ k, middleHeaderTargets k ≠ middleWork (middleTranslation j)) i hi width modulus))
    (blankL 23 (by decide)) (right 23 (by decide) (by decide))
    (by intro i x
        change _ = readAt blank (H.L (ports i)) (H.R (ports i)) _
        change _ = readAt blank (H.L ((sim i).castAdd 31)) (H.R ((sim i).castAdd 31)) _
        rw [left,caller (sim i)]
        exact initial i x)
  have full := Exec.seq copy run
  change Exec body prog (mk u S) (((List.finRange 6).map fun i => 6*(S.R (fromTape i)).length+6).sum+1+n) (mk z D) at full
  rw [middleHeaderCost S fromTape headers] at full
  let steps := (6*(P.size+G.size+3*M.size+B.size)+37)+n
  have completed : Exec body prog (mk u S) steps (mk z D) := full
  have time : steps ≤ budget := Nat.add_le_add_left hn _
  obtain ⟨z',J,k,hu,bound,finished,keep,empty⟩ := releaseMiddleWork body prog completed time hp hbody free
  refine ⟨z',J,k,hu.trans (hz.trans hb),bound,finished,?_,?_,empty,?_⟩
  · intro i x
    change _ = readAt blank (J.L ((sim i).castAdd 31)) (J.R ((sim i).castAdd 31)) _
    rw [(keep (sim i)).1,(keep (sim i)).2]
    exact rep i x
  · intro x
    change readAt blank (J.L ((sim slot).castAdd 31)) (J.R ((sim slot).castAdd 31)) _ = _
    rw [(keep (sim slot)).1,(keep (sim slot)).2]
    exact out x
  · intro j hj
    have preserved := off j hj
    rw [(keep j).1,(keep j).2,preserved.1,preserved.2,left,caller j]
    exact ⟨rfl,rfl⟩

theorem loadedMiddleShear_exec {K Q : ℕ} (slot : Fin K) (capacity : 217 ≤ Q)
    (w c : ℕ) (radix : M = prime^(w+1)) (hc : c < M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (word : Fin ((P*M*G)*(M*B)) → ZMod 2) (src : Fin 6 → Fin K) :
      let bank := Record.payloadBank slot (22 : Fin 31)
      let shear := statePlacedNormalized bank capacity (by decide : 0 < 217) Empty.elim
        initializedMiddleShear
      let N := (P*M*G)*(M*B)
      let xs := FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)
      ∀ (body : F → Pr F (K+31) Q prime U)
        (u : HS (K+31) Q prime U) (S : Stacks (K+31) prime),
        let fromTape := fun i => (src i).castAdd 31
        let targets := middleHeaderTargets.trans (Fin.natAddEmb K)
        let setup : Pr F (K+31) Q prime U := Record.copyLeafHeaders fromTape targets ((4 : Fin 31).natAdd K)
          ((5 : Fin 31).natAdd K) (List.finRange 6)
        let prog := setup.seq shear
        let work := (List.finRange 31).map (Fin.natAddEmb K)
        let budget := (6*(P.size+G.size+3*M.size+B.size)+37)+((6*M.size+9)+
          (210*(2*(Nat.size prime+1)^2)+16120)*N)
        ∀ push, Fast.Main.mnProgPush prog ≤ push → (∀ f, Fast.Main.mnProgPush (body f) ≤ push) →
        (∀ j : Fin 31, S.L (j.natAdd K) = [] ∧ S.R (j.natAdd K) = []) →
        (∀ i, S.R (fromTape i) = (![binSyms P.size P,binSyms G.size G,binSyms M.size c,
          binSyms M.size 0,binSyms B.size B,binSyms M.size M] i)) →
          (∀ x, readAt blank (S.L (slot.castAdd 31)) (S.R (slot.castAdd 31)) x = leafBitTape (List.ofFn word) x) →
          ∃ z D n, z.user = u.user ∧
            n ≤ budget+(125+31*(6*(push*budget))) ∧
            Exec body (prog.seq (clearWorkTapes work)) (mk u S) n (mk z D) ∧
            (∀ x, readAt blank (D.L (slot.castAdd 31)) (D.R (slot.castAdd 31)) x = leafBitTape xs x) ∧
            (∀ j : Fin 31, D.L (j.natAdd K) = [] ∧ D.R (j.natAdd K) = []) ∧
            ∀ j : Fin K, j ≠ slot →
              D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31) := by
  intro bank shear N xs body u S fromTape targets setup prog work budget push hp hbody free headers initial
  obtain ⟨b,H,hb,copy,left,loaded,caller,unused⟩ := copyMiddleHeaders_exec body src u S (fun j => (free j).2)
  let E := embStk bank H
  have entry (i : Fin 6) : E.R (middleHeaderTargets i) =
      (![binSyms P.size P,binSyms G.size G,binSyms M.size c,binSyms M.size 0,binSyms B.size B,binSyms M.size M] i) :=
    calc E.R (middleHeaderTargets i) = H.R (targets i) := by
           change H.R (bank _) = _
           rw [show bank (middleHeaderTargets i) = (middleHeaderTargets i).natAdd K from
             Record.payloadBank_private slot 22 _ ((by decide : ∀ j, middleHeaderTargets j ≠ 22) i)]
           rfl
         _ = _ := (loaded i).trans (headers i)
  have right (j : Fin 31) (privateSlot : j ≠ 22) (off : ∀ i, middleHeaderTargets i ≠ j) : E.R j = [] := by
    change H.R (Record.payloadBank slot 22 j) = []
    rw [Record.payloadBank_private _ _ _ privateSlot]
    exact unused j off
  have blankL (j : Fin 31) (privateSlot : j ≠ 22) : E.L j = [] := by
    change H.L (Record.payloadBank slot 22 j) = []
    rw [left,Record.payloadBank_private _ _ _ privateSlot]
    exact (free j).1
  obtain ⟨z,D,n,hz,hn,run,out,off⟩ := placedMiddleShear_exec slot capacity w c radix hc hP hG hB
    word body b H (entry 0) (entry 1)
    (fun i lo hi => right _ ((by decide : ∀ j : Fin 30, 24 ≤ j → j ≤ 27 → middleWork j ≠ 22) i lo hi)
      ((by decide : ∀ j : Fin 30, 24 ≤ j → j ≤ 27 → ∀ k, middleHeaderTargets k ≠ middleWork j) i lo hi))
    (entry 2) (entry 3) (right 2 (by decide) (by decide))
    (fun i lo hi => right _ ((by decide : ∀ j : Fin 13, middleWork (middleArithmetic j) ≠ 22) i)
      ((by decide : ∀ j : Fin 13, 3 ≤ j → j < 12 → ∀ k, middleHeaderTargets k ≠ middleWork (middleArithmetic j)) i lo hi))
    (blankL 30 (by decide)) (right 30 (by decide) (by decide))
    (fun i hi => blankL _ ((by decide : ∀ j : Fin 12, j < 10 → middleWork (middleTranslation j) ≠ 22) i hi))
    (by intro i hi
        by_cases width : i = 5
        · subst i; exact entry 4
        by_cases modulus : i = 7
        · subst i; exact entry 5
        simp only [ite_eq_right width,ite_eq_right modulus]
        exact right _ ((by decide : ∀ j : Fin 12, j < 10 → middleWork (middleTranslation j) ≠ 22) i hi)
          ((by decide : ∀ j : Fin 12, j < 10 → j ≠ 5 → j ≠ 7 → ∀ k, middleHeaderTargets k ≠ middleWork (middleTranslation j)) i hi width modulus))
    (blankL 23 (by decide)) (right 23 (by decide) (by decide))
    (by intro x
        rw [left,caller slot]
        exact initial x)
  have full := Exec.seq copy run
  change Exec body prog (mk u S) (((List.finRange 6).map fun i => 6*(S.R (fromTape i)).length+6).sum+1+n) (mk z D) at full
  rw [middleHeaderCost S fromTape headers] at full
  let steps := (6*(P.size+G.size+3*M.size+B.size)+37)+n
  have completed : Exec body prog (mk u S) steps (mk z D) := full
  have time : steps ≤ budget := Nat.add_le_add_left hn _
  obtain ⟨z',J,k,hu,bound,finished,keep,empty⟩ := releaseMiddleWork body prog completed time hp hbody free
  refine ⟨z',J,k,hu.trans (hz.trans hb),bound,finished,?_,empty,?_⟩
  · intro x
    rw [(keep slot).1,(keep slot).2]
    exact out x
  · intro j hj
    have preserved := off j hj
    rw [(keep j).1,(keep j).2,preserved.1,preserved.2,left,caller j]
    exact ⟨rfl,rfl⟩

/-- Run the two shear-and-swap occurrences with distinct coefficient headers.
The second occurrence reuses the released workspace and the first output word. -/
theorem twoMiddleSwaps_exec [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (size : (P*M*G)*(M*B) = volume prime v) (w : ℕ) (radix : M = prime^(w+1))
    (c : Bool → Fin M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (word : Fin ((P*M*G)*(M*B)) → ZMod 2) (io : Fin T) (roles : Tapes T prime)
    (head : roles.head io = 0) (input : roles.tape io = leafBitTape (List.ofFn word))
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let block := LeafCore.core io
    ∀ {K : ℕ} (sim : Fin block.tapes ↪ Fin K) (src : Bool → Fin 6 → Fin K)
      (_apart : ∀ i j, sim i ≠ src true j) (slot : Fin block.tapes) (_leading : slot.val = io.val)
      (capacity : 217 ≤ block.states),
      let ports := sim.trans (Fin.castAddEmb 31)
      let shear := statePlacedNormalized (Record.payloadBank (sim slot) (22 : Fin 31)) capacity
        (by decide : 0 < 217) Empty.elim initializedMiddleShear
      let prog := fun b => (Record.copyLeafHeaders (fun i => (src b i).castAdd 31)
        (middleHeaderTargets.trans (Fin.natAddEmb K)) ((4 : Fin 31).natAdd K) ((5 : Fin 31).natAdd K) (List.finRange 6)).seq
        (.seq shear (embProg ports Empty.elim (foreign block.program)))
      let work := (List.finRange 31).map (Fin.natAddEmb K)
      let stage := fun b => (prog b).seq (clearWorkTapes work)
      let result := fun b x => swapLeafList v size (FiberLayoutData.translated x
        (fun i => (c b).val*(i.val/G%M)%M)) (FiberLayoutData.translated_length ..)
      let y := result true (result false word)
      let budget := (6*(P.size+G.size+3*M.size+B.size)+37)+((6*M.size+9)+
        (210*(2*(Nat.size prime+1)^2)+16120)*((P*M*G)*(M*B))+(LeafCore.coreCost (volume prime v) v.width*(block.tapes+5)+6))
      ∀ (body : F → Pr F (K+31) block.states prime U) (u : HS (K+31) block.states prime U)
        (S : Stacks (K+31) prime) push, (∀ b, Fast.Main.mnProgPush (prog b) ≤ push) →
        (∀ f, Fast.Main.mnProgPush (body f) ≤ push) →
        (∀ j : Fin 31, S.L (j.natAdd K) = [] ∧ S.R (j.natAdd K) = []) →
        (∀ b i, S.R ((src b i).castAdd 31) = (![binSyms P.size P,binSyms G.size G,binSyms M.size (c b).val,
          binSyms M.size 0,binSyms B.size B,binSyms M.size M] i)) →
        RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
        ∃ z D n, z.user = u.user ∧ n ≤ 2*(budget+(125+31*(6*(push*budget)))) ∧
          Exec body ((stage false).seq (stage true)) (mk u S) n (mk z D) ∧
          RepT (raw (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn y)) 0)
            (Routines.hdr v) f p node scalar ctr st) block.tapes) (D.L ∘ ports) (D.R ∘ ports) ∧
          (∀ x, readAt blank (D.L (ports slot)) (D.R (ports slot)) x = leafBitTape (List.ofFn y) x) ∧
          (∀ j : Fin 31, D.L (j.natAdd K) = [] ∧ D.R (j.natAdd K) = []) ∧
          ∀ j : Fin K, (∀ i, sim i ≠ j) →
            D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31) := by
  intro block K sim src apart slot leading capacity ports shear prog work stage result y budget body u S push hp hb free headers initial
  obtain ⟨b,H,n,hu,hn,run,rep,_,clean,keep⟩ := loadedMiddleSwap_exec v positive size w _ radix
    (c false).isLt hP hG hB word io roles head input f p node scalar ctr st sim (src false) slot capacity
    leading body u S push (hp false) hb free (headers false) initial
  let roles' := SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn (result false word))) 0
  obtain ⟨z,D,m,hz,hm,next,out,read,empty,preserved⟩ := loadedMiddleSwap_exec v positive size w _ radix
    (c true).isLt hP hG hB (result false word) io roles' (by simp [roles',SharedPlacementAlphabet.setTape])
    (by simp [roles',SharedPlacementAlphabet.setTape]) f p node scalar ctr st sim (src true) slot capacity
    leading body b H push (hp true) hb clean
    (fun i => ((keep _ (fun j => apart j i)).2).trans (headers true i)) rep
  refine ⟨z,D,n+m,hz.trans hu,?_,Exec.seq run next,?_,read,empty,?_⟩
  · rw [two_mul]
    exact Nat.add_le_add hn hm
  · simpa only [roles',SharedPlacementAlphabet.setTape,Function.update_idem] using out
  · intro j hj
    exact ⟨(preserved j hj).1.trans (keep j hj).1,(preserved j hj).2.trans (keep j hj).2⟩

noncomputable def middleShearsCost [M8.Machine.Net] (P M G B V width tapes push : ℕ) : ℕ :=
  let budget := (6*(P.size+G.size+3*M.size+B.size)+37)+((6*M.size+9)+
        (210*(2*(Nat.size prime+1)^2)+16120)*((P*M*G)*(M*B))+(LeafCore.coreCost V width*(tapes+5)+6))
  let lastBudget := (6*(P.size+G.size+3*M.size+B.size)+37)+((6*M.size+9)+
        (210*(2*(Nat.size prime+1)^2)+16120)*((P*M*G)*(M*B)))
  2*(budget+(125+31*(6*(push*budget)))) + (lastBudget+(125+31*(6*(push*lastBudget))))

theorem threeMiddleShears_exec [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (size : (P*M*G)*(M*B) = volume prime v) (w : ℕ) (radix : M = prime^(w+1))
    (c : Bool → Fin M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (word : Fin ((P*M*G)*(M*B)) → ZMod 2) (io : Fin T) (roles : Tapes T prime)
    (head : roles.head io = 0) (input : roles.tape io = leafBitTape (List.ofFn word))
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let block := LeafCore.core io
    ∀ {K : ℕ} (sim : Fin block.tapes ↪ Fin K) (src : Bool → Fin 6 → Fin K)
      (_apart : ∀ b i j, sim i ≠ src b j) (slot : Fin block.tapes) (_leading : slot.val = io.val)
      (capacity : 217 ≤ block.states),
      let ports := sim.trans (Fin.castAddEmb 31)
      let shear := statePlacedNormalized (Record.payloadBank (sim slot) (22 : Fin 31)) capacity
        (by decide : 0 < 217) Empty.elim initializedMiddleShear
      let prog := fun b => (Record.copyLeafHeaders (fun i => (src b i).castAdd 31)
        (middleHeaderTargets.trans (Fin.natAddEmb K)) ((4 : Fin 31).natAdd K) ((5 : Fin 31).natAdd K) (List.finRange 6)).seq
        (.seq shear (embProg ports Empty.elim (foreign block.program)))
      let lastProg := (Record.copyLeafHeaders (fun i => (src false i).castAdd 31)
        (middleHeaderTargets.trans (Fin.natAddEmb K)) ((4 : Fin 31).natAdd K) ((5 : Fin 31).natAdd K) (List.finRange 6)).seq shear
      let work := (List.finRange 31).map (Fin.natAddEmb K)
      let stage := fun b => (prog b).seq (clearWorkTapes work)
      let result := fun b x => swapLeafList v size (FiberLayoutData.translated x
        (fun i => (c b).val*(i.val/G%M)%M)) (FiberLayoutData.translated_length ..)
      let y := result true (result false word)
      ∀ (body : F → Pr F (K+31) block.states prime U) (u : HS (K+31) block.states prime U)
        (S : Stacks (K+31) prime) push, (∀ b, Fast.Main.mnProgPush (prog b) ≤ push) →
        Fast.Main.mnProgPush lastProg ≤ push → (∀ f, Fast.Main.mnProgPush (body f) ≤ push) →
        (∀ j : Fin 31, S.L (j.natAdd K) = [] ∧ S.R (j.natAdd K) = []) →
        (∀ b i, S.R ((src b i).castAdd 31) = (![binSyms P.size P,binSyms G.size G,binSyms M.size (c b).val,
          binSyms M.size 0,binSyms B.size B,binSyms M.size M] i)) →
        RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
        ∃ z D n, z.user = u.user ∧ n ≤ middleShearsCost P M G B (volume prime v) v.width block.tapes push ∧
          Exec body (((stage false).seq (stage true)).seq (lastProg.seq (clearWorkTapes work))) (mk u S) n (mk z D) ∧
          RepT (raw (CommonBank.bank (SharedPlacementAlphabet.setTape roles io
            (leafBitTape (FiberLayoutData.translated y (fun i => (c false).val*(i.val/G%M)%M))) 0)
            (Routines.hdr v) f p node scalar ctr st) block.tapes) (D.L ∘ ports) (D.R ∘ ports) ∧
          (∀ x, readAt blank (D.L (ports slot)) (D.R (ports slot)) x = leafBitTape (FiberLayoutData.translated y (fun i => (c false).val*(i.val/G%M)%M)) x) ∧
          (∀ j : Fin 31, D.L (j.natAdd K) = [] ∧ D.R (j.natAdd K) = []) ∧
          ∀ j : Fin K, (∀ i, sim i ≠ j) →
            D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31) := by
  intro block K sim src apart slot leading capacity ports shear prog lastProg work stage result y body u S push hp hl hb free headers initial
  obtain ⟨b,H,n,hu,hn,run,rep,read,clean,keep⟩ := twoMiddleSwaps_exec v positive size w radix c hP hG hB
    word io roles head input f p node scalar ctr st sim src (apart true) slot leading capacity body u S push hp hb free headers initial
  obtain ⟨z,D,m,hz,hm,last,out,empty,preserved⟩ := loadedMiddleShear_exec (sim slot) capacity w _ radix
    (c false).isLt hP hG hB y (src false) body b H push hl hb clean
    (fun i => ((keep _ (fun j => apart false j i)).2).trans (headers false i))
    (by simpa only [Function.Embedding.trans_apply, Fin.castAddEmb_apply] using read)
  refine ⟨z,D,n+m,hz.trans hu,(by dsimp only [middleShearsCost,block]; exact Nat.add_le_add hn hm),Exec.seq run last,?_,?_,empty,?_⟩
  · have updated := leafBank_writeRole v io (SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn y)) 0)
        f p node scalar ctr st _ ports H D slot leading rep
        (fun i hi => preserved (sim i) (sim.injective.ne hi)) out
    simpa only [SharedPlacementAlphabet.setTape,Function.update_idem] using updated
  · simpa only [ports,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using out
  · intro j hj
    have same := preserved j (hj slot).symm
    exact ⟨same.1.trans (keep j hj).1,same.2.trans (keep j hj).2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
