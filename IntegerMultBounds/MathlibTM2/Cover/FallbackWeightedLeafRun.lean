module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackMiddleSwap
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafSignRun

/-! Run the weighted leaf word on the shared caller payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout SharedBankStageInput
variable {T P M G B : ℕ} {F U : Type}

theorem signedMiddleShears_exec [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (size : (P*M*G)*(M*B) = volume prime v) (w : ℕ) (radix : M = prime^(w+1))
    (odd : Odd M) (c : Bool → Fin M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
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
      let xs := FiberLayoutData.translated y (fun i => (c false).val*(i.val/G%M)%M)
      let len : xs.length = P*(M*(G*(M*B))) := by rw [FiberLayoutData.translated_length]; simp [Nat.mul_assoc]
      let signWord := fun i => xs.get (Fin.cast len.symm i)
      let signSrc := fun i : Fin 4 => src false (![0,1,5,4] i)
      let load := Record.copyLeafHeaders (fun i => (signSrc i).castAdd 31) (signHeaderTargets.trans (Fin.natAddEmb K))
        ((1 : Fin 31).natAdd K) ((2 : Fin 31).natAdd K) (List.finRange 4)
      let bank := signWork.trans (Record.payloadBank (sim slot) (0 : Fin 31))
      let child := (leafSignSetup (F := Empty)).seq (embProg (Fin.castAddEmb 2) Empty.elim leafSignReturn)
      let sign := load.seq (statePlacedNormalized bank capacity (by decide) Empty.elim child)
      let budget := (6*(P.size+G.size+3*M.size+B.size)+37)+((6*M.size+9)+
        (210*(2*(Nat.size prime+1)^2)+16120)*((P*M*G)*(M*B))+(LeafCore.coreCost (volume prime v) v.width*(block.tapes+5)+6))
      let lastBudget := (6*(P.size+G.size+3*M.size+B.size)+37)+((6*M.size+9)+
        (210*(2*(Nat.size prime+1)^2)+16120)*((P*M*G)*(M*B)))
      ∀ (body : F → Pr F (K+31) block.states prime U) (u : HS (K+31) block.states prime U)
        (S : Stacks (K+31) prime) push, (∀ b, Fast.Main.mnProgPush (prog b) ≤ push) →
        Fast.Main.mnProgPush lastProg ≤ push → (∀ f, Fast.Main.mnProgPush (body f) ≤ push) →
        (∀ j : Fin 31, S.L (j.natAdd K) = [] ∧ S.R (j.natAdd K) = []) →
        (∀ b i, S.R ((src b i).castAdd 31) = (![binSyms P.size P,binSyms G.size G,binSyms M.size (c b).val,
          binSyms M.size 0,binSyms B.size B,binSyms M.size M] i)) →
        RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
        ∃ z D n, z.user = u.user ∧ n ≤ (2*(budget+(125+31*(6*(push*budget)))) + (lastBudget+(125+31*(6*(push*lastBudget))))) + ((6*(P.size+G.size+M.size+B.size)+25)+(1+leafSignCost P G M B)) ∧
          Exec body ((((stage false).seq (stage true)).seq (lastProg.seq (clearWorkTapes work))).seq sign) (mk u S) n (mk z D) ∧
          (∀ x, readAt blank (D.L (ports slot)) (D.R (ports slot)) x = leafBitTape (negateLeafHead signWord) x) ∧
          (∀ [NeZero M], P = v.beforeRows*v.rows*v.beforeH → G = v.between → B = v.afterD →
            ∀ (_radixWidth : prime^v.width = M) (weight inv : ZMod M), weight*inv = 1 →
            (c false).val = inv.val → (c true).val = (-weight).val →
            ∀ (a : Fin v.beforeRows) (row : Fin v.rows) (pre : Fin v.beforeH)
              (mid : Fin v.between) (post : Fin v.afterD) (h t : ZMod M),
              (negateLeafHead signWord)[index prime v a row pre (weight*t).val mid (inv*h).val post]? =
                (List.ofFn word)[index prime v a row pre h.val mid t.val post]?) ∧
          ∀ j : Fin K, (∀ i, sim i ≠ j) →
            D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31) := by
  intro block K sim src apart slot leading capacity ports shear prog lastProg work stage result y xs len signWord signSrc load bank child sign budget lastBudget body u S push hp hl hb free headers initial
  obtain ⟨b,H,n,hu,hn,run,read,clean,keep⟩ := threeMiddleShears_exec v positive size w radix c hP hG hB
    word io roles head input f p node scalar ctr st sim src apart slot leading capacity body u S push hp hl hb free headers initial
  have data : List.ofFn signWord = xs := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using len.symm
    · intros; simp [signWord]
  have hM : 0 < M := radix ▸ pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _
  obtain ⟨z,D,m,hz,hm,last,out,frame⟩ := loadedLeafSign_exec (sim slot) capacity hP hG hM hB odd signWord signSrc
    body b H (by simpa only [data,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using read)
    (by intro i
        rw [(keep _ (fun j => apart false j (![0,1,5,4] i))).2]
        fin_cases i <;> first | exact headers false 0 | exact headers false 1 | exact headers false 5 | exact headers false 4) clean
  refine ⟨z,D,n+m,hz.trans hu,Nat.add_le_add hn hm,Exec.seq run last,?_,?_,?_⟩
  · simpa only [ports,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using out
  · intro inst prefixEq gapEq widthEq radixWidth weight inv unit firstCoeff middleCoeff
    subst P; subst G; subst B
    have coeff : c = fun b => if b then ⟨(-weight).val,(-weight).val_lt⟩ else ⟨inv.val,inv.val_lt⟩ := by
      funext b
      cases b
      · exact Fin.ext firstCoeff
      · exact Fin.ext middleCoeff
    subst c
    exact
      weightedLeafOutput_entry v radixWidth weight inv unit word
  · intro j hj
    have same := frame j (hj slot).symm
    exact ⟨same.1.trans (keep j hj).1,same.2.trans (keep j hj).2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
