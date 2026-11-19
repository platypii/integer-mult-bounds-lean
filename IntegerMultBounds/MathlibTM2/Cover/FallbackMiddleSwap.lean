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

noncomputable def initializedMiddleShear : Pr Empty 31 217 prime U :=
  .seq (.act (.push (.lt 30) (fun _ => separator) .done)) (.seq (initializeBank (middleTranslation.trans middleWork))
    (returnedMiddleShear (Function.Embedding.refl _)))

theorem middleSwap_exec [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (size : (P*M*G)*(M*B) = volume prime v) (w c : ℕ) (radix : M = prime^(w+1))
    (hc : c < M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (word : Fin ((P*M*G)*(M*B)) → ZMod 2) (io : Fin T) (roles : Tapes T prime)
    (head : roles.head io = 0) (input : roles.tape io = leafBitTape (List.ofFn word))
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let block := LeafCore.core io
    let ports := Fin.castAddEmb (n := block.tapes) 31
    ∀ (slot : Fin block.tapes) (capacity : 217 ≤ block.states), slot.val = io.val →
      let bank := Record.payloadBank slot (22 : Fin 31)
      let shear := statePlacedNormalized bank capacity (by decide : 0 < 217) Empty.elim
        initializedMiddleShear
      let N := (P*M*G)*(M*B)
      let xs := FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)
      let y := swapLeafList v size xs (FiberLayoutData.translated_length ..)
      ∀ (body : F → Pr F (block.tapes+31) block.states prime U)
        (u : HS (block.tapes+31) block.states prime U) (S : Stacks (block.tapes+31) prime),
        let E := embStk bank S
        ∀ bs ms, Counter.value bs = B → Counter.value ms = M →
          GrowingCounterData.Canonical bs → GrowingCounterData.Canonical ms →
          E.R 28 = binSyms P.size P → E.R 29 = binSyms G.size G →
          (∀ i : Fin 30, 24 ≤ i → i ≤ 27 → E.R (middleWork i) = []) →
          E.R 0 = binSyms M.size c → E.R 1 = binSyms M.size 0 → E.R 2 = binSyms M.size M →
          (∀ i : Fin 13, 3 ≤ i → i < 12 → E.R (middleWork (middleArithmetic i)) = []) →
          E.L 30 = [] → E.R 30 = [] →
          (∀ i : Fin 12, i < 10 → E.L (middleWork (middleTranslation i)) = []) →
          (∀ i : Fin 12, i < 10 → E.R (middleWork (middleTranslation i)) =
            if i = 5 then bs.map bitSymbol else if i = 7 then ms.map bitSymbol else []) →
          E.L 23 = [] → E.R 23 = [] →
          RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
          ∃ z D n, z.user = u.user ∧
            n ≤ 3+(210*(2*(Nat.size prime+1)^2)+16120)*N+(LeafCore.coreCost (volume prime v) v.width*(block.tapes+5)+6) ∧
            Exec body (.seq shear (embProg ports Empty.elim (foreign block.program))) (mk u S) n (mk z D) ∧
            RepT (raw (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn y)) 0)
              (Routines.hdr v) f p node scalar ctr st) block.tapes) (D.L ∘ ports) (D.R ∘ ports) ∧
            ∀ x, readAt blank (D.L (ports slot)) (D.R (ports slot)) x = leafBitTape (List.ofFn y) x := by
  intro block ports slot capacity leading bank shear N xs y body u S E bs ms hb hm cb cm heads ticks free coef digit modulus scratch marker fresh left right dl dr initial
  have shared : bank 22 = ports slot := Record.payloadBank_shared slot 22
  have cell := initial slot
  have inside : slot.val < CommonBank.count T := leading ▸ (LeafCore.roleSlot io).isLt
  have same : (⟨slot.val,inside⟩ : Fin (CommonBank.count T)) = LeafCore.roleSlot io := Fin.ext leading
  obtain ⟨hh,ht⟩ := LeafCore.bank_role roles (Routines.hdr v) f p node scalar ctr st io
  have src (x : ℤ) : RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ word)) x) =
      readAt blank (E.L 22) (E.R 22) x := by
    change _ = readAt blank (S.L (bank 22)) (S.R (bank 22)) x
    rw [shared]
    simpa only [raw,dite_eq_left inside,same,hh,ht,head,input,leafBitTape,List.map_ofFn,sub_zero,
      Function.comp_apply] using cell x
  let u₀ := stateLiftDown (by decide : 0 < 217) (embDn bank u)
  let markedE : Stacks 31 prime := {E with L := Function.update E.L 30 [separator]}
  have mark := Exec.act (body := (Empty.elim : Empty → Pr Empty 31 217 prime U))
    (.push (.lt 30) (fun _ => separator) .done) (mk u₀ E)
  have install : Exec Empty.elim (.act (.push (.lt 30) (fun _ => separator) .done))
      (mk u₀ E) 1 (mk u₀ markedE) := by
    simpa [markedE,Action.run,update_lt,store_mk,marker] using mark
  have untouched (i : Fin 12) : markedE.L (middleWork (middleTranslation i)) =
      E.L (middleWork (middleTranslation i)) :=
    Function.update_of_ne ((by decide : ∀ j, middleWork (middleTranslation j) ≠ 30) i) _ _
  obtain ⟨I,init,rs,marked,keep,rep⟩ := initializeBank_exec (P := Empty) Empty.elim
    (middleTranslation.trans middleWork) bs ms
    (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ word))) (fun _ => blank) 0 0
    u₀ markedE (fun i hi => (untouched i).trans (left i hi)) right
    (by intro x; rw [sub_zero]; change _ = readAt blank (markedE.L (middleWork (middleTranslation 10))) (E.R 22) x; rw [untouched]; exact src x) (by
      intro x
      change blank = readAt blank (markedE.L 23) (E.R 23) (x-0)
      simp [markedE,Function.update_of_ne,dl,dr,readAt_nil_left,wordTape_nil])
  have ready : MiddleGroupReady middleArithmetic M.size c 0 M (embStk middleWork I) :=
    by
    change I.R 0 = _ ∧ I.R 1 = _ ∧ I.R 2 = _ ∧ (∀ i : Fin 13, 3 ≤ i → i < 12 →
      I.R (middleWork (middleArithmetic i)) = []) ∧ I.L 3 = _
    rw [rs]
    exact ⟨coef,digit,modulus,scratch,marked⟩
  obtain ⟨a,D,n,ha,hn,run,payload,_⟩ := returnedMiddleShear_exec (F := Empty) Empty.elim (Function.Embedding.refl _)
    w c radix hc hP hG hB (fun _ => blank) (fun _ => blank) 0 0 (SparseRoleCircuit.encode ∘ word)
    bs ms hb hm cb cm u₀ I (rs ▸ heads) (rs ▸ ticks) (rs ▸ free) ready
    ((keep 30 (by decide)).trans (by simp [markedE])) (rs ▸ fresh) rep (fun _ _ _ => rfl)
  obtain ⟨b,H,hb',placed,eq,frame⟩ := Record.payloadFrame_exec capacity slot (22 : Fin 31) (by decide)
    body initializedMiddleShear u S a D (1+(1+n)) (Exec.seq install (Exec.seq init run))

  have read := payload
  rw [← eq] at read
  change ∀ x, readAt blank (H.L (bank 22)) (H.R (bank 22)) (x-0) = _ at read
  rw [shared] at read
  obtain ⟨z,J,k,hz,hk,exec,result,out,_⟩ := swapReturnedShear_exec v positive size word
    (fun i => c*(i.val/G%M)%M) io roles f p node scalar ctr st ports body shear u b S H slot (1+(1+(1+n)))
    leading initial placed (hb'.trans ha) frame (by simpa only [sub_zero] using read)
  have bound := Nat.add_le_add_right (Nat.add_le_add_left hn 3) (LeafCore.coreCost (volume prime v) v.width*(block.tapes+5)+6)
  exact ⟨z,J,k,hz,hk.trans (by simpa only [← Nat.add_assoc] using bound),exec,result,out⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
