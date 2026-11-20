module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafFrame
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafNegation

/-! Load the three runtime volume factors and return a coordinate word to the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

def returnHeaderTargets : Fin 3 ↪ Fin 10 := ⟨![3,5,7],by decide⟩

theorem stagedLeafReturn_exec {P M B T Q : ℕ} {F U : Type} (hP : 0 < P) (hM : 0 < M) (hB : 0 < B)
    (capacity : 217 ≤ Q) (body : F → Pr F T Q prime U) (r : Fin 10 ↪ Fin T)
    (header : Fin 3 → Fin T) (apart : ∀ i j, header i ≠ r j)
    (v : HS T Q prime U) (S : Stacks T prime) (source : ℤ → Fin 4) (p : ℤ)
    (xs : List (ZMod 2)) (hx : xs.length = P*(M*B))
    (dst : ∀ z, readAt blank (S.L (r 0)) (S.R (r 0)) z = leafBitTape xs z)
    (src : ∀ z, readAt blank (S.L (r 1)) (S.R (r 1)) (z-p) = RadixToBinary.binaryEncoding.encode (source z))
    (words : ∀ i, S.R (header i) = ![binSyms B.size B,binSyms M.size M,binSyms P.size P] i)
    (empty : ∀ i : Fin 10, 2 ≤ i.val → S.L (r i) = [] ∧ S.R (r i) = []) :
    let ports := (Fin.castAddEmb (n := 8) 2).trans r
    let setup := Record.copyLeafHeaders header (returnHeaderTargets.trans r) (r 8) (r 9) (List.finRange 3)
    let localRun : Pr Empty 8 217 prime U := (.act (pushMarkers [2,3,4,5,6,7]) : Pr Empty 8 217 prime U).seq
      (returnFromOrigin (Function.Embedding.refl _))
    ∃ u D n, u.user = v.user ∧ n ≤ 6*(B.size+M.size+P.size)+19+((218*(P*(M*B))+1)*13+8) ∧
      Exec body (setup.seq (statePlacedNormalized ports capacity (by decide) Empty.elim localRun)) (mk v S) n (mk u D) ∧
      (∀ z, readAt blank (D.L (r 1)) (D.R (r 1)) (z-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (xs.map SparseRoleCircuit.encode) z)) ∧
      ∀ j, (∀ i, r i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  intro ports setup localRun
  have distinct (i : Fin 3) : [header i,(returnHeaderTargets.trans r) i,r 8,r 9].Nodup := by
    have nd := ((by decide : ∀ k, [returnHeaderTargets k,8,9].Nodup) i).map r.injective
    exact List.nodup_cons.mpr ⟨by simp [apart],nd⟩
  obtain ⟨y,E,user,copy,left,loaded,off⟩ := Record.copyLeafHeaders_exec body header (returnHeaderTargets.trans r)
    (r 8) (r 9) (fun i j => apart i (returnHeaderTargets j)) distinct _ (List.nodup_finRange 3) v S
    (empty 8 (by decide)).2 (empty 9 (by decide)).2 (fun i _ => (empty _ ((by decide : ∀ k, 2 ≤ (returnHeaderTargets k).val) i)).2)
  have keep (j : Fin 10) (h : ∀ i, returnHeaderTargets i ≠ j) := off (r j) (fun i _ => r.injective.ne (h i))
  have ready (i : Fin 6) : E.L (ports (Fin.natAdd 2 i)) = [] ∧ E.R (ports (Fin.natAdd 2 i)) =
      ![[],binSyms B.size B,[],binSyms M.size M,[],binSyms P.size P] i := by
    constructor
    · rw [left]; exact (empty _ ((by decide : ∀ k : Fin 6, 2 ≤ ((Fin.natAdd 2 k).castAdd 2).val) i)).1
    · fin_cases i <;> first
        | exact (loaded _ (List.mem_finRange _)).trans (words 0)
        | exact (loaded _ (List.mem_finRange _)).trans (words 1)
        | exact (loaded _ (List.mem_finRange _)).trans (words 2)
        | exact (keep _ (by decide)).trans (empty _ (by decide)).2
  obtain ⟨u,D,n,hu,time,run,out,frame⟩ := placedLeafReturn_exec hP hM hB capacity body ports y E source p xs hx
    (by intro z; change readAt blank (E.L (r 0)) (E.R (r 0)) z = _; rw [left,keep 0 (by decide)]; exact dst z)
    (by intro z; change readAt blank (E.L (r 1)) (E.R (r 1)) _ = _; rw [left,keep 1 (by decide)]; exact src z) ready
  refine ⟨u,D,_,hu.trans user,?_,Exec.seq copy run,out,?_⟩
  · simp only [show List.finRange 3 = [0,1,2] by decide,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,words,Matrix.cons_val_zero,Matrix.cons_val_one,length_binSyms]
    simp [length_binSyms]
    omega
  · intro j outside
    have f := frame j (fun i => outside (i.castAdd 2))
    exact ⟨f.1.trans (congrFun left j),f.2.trans (off j (fun i _ => outside (returnHeaderTargets i)))⟩

/-- Run a private coordinate program and return its role word to a saved caller tape.
The caller's three headers stay outside the coordinate bank throughout the run. -/
theorem coordinateReturn_exec {P M B T Q : ℕ} {F U : Type} (hP : 0 < P) (hM : 0 < M) (hB : 0 < B)
    (capacity : 217 ≤ Q) (body : F → Pr F (13+T) Q prime U) (io : Fin T)
    (coordinate : Pr Empty T Q prime U) (v : HS (13+T) Q prime U) (S : Stacks (13+T) prime)
    (source : ℤ → Fin 4) (p : ℤ) (xs : List (ZMod 2)) (hx : xs.length = P*(M*B)) :
    let bank := Fin.natAddEmb 13 (m := T)
    let outer := Fin.castAddEmb (n := 13) T
    let r := ((Fin.castAddEmb (n := 10) 3).trans outer).trans (Equiv.swap (outer 0) (bank io)).toEmbedding
    let header := fun i : Fin 3 => outer (i.natAdd 10)
    let setup := Record.copyLeafHeaders header (returnHeaderTargets.trans r) (r 8) (r 9) (List.finRange 3)
    let localRun : Pr Empty 8 217 prime U := (.act (pushMarkers [2,3,4,5,6,7]) : Pr Empty 8 217 prime U).seq
      (returnFromOrigin (Function.Embedding.refl _))
    let finish := setup.seq (statePlacedNormalized ((Fin.castAddEmb 2).trans r) capacity (by decide) Empty.elim localRun)
    ∀ w E t, Exec Empty.elim coordinate (mk (embDn bank v) (embStk bank S)) t (mk w E) →
      w.user = v.user → (∀ z, readAt blank (E.L io) (E.R io) z = leafBitTape xs z) →
      (∀ z, readAt blank (S.L (outer 1)) (S.R (outer 1)) (z-p) = RadixToBinary.binaryEncoding.encode (source z)) →
      (∀ i, S.R (header i) = ![binSyms B.size B,binSyms M.size M,binSyms P.size P] i) →
      (∀ i : Fin 10, 2 ≤ i.val → S.L (outer (i.castAdd 3)) = [] ∧ S.R (outer (i.castAdd 3)) = []) →
      ∃ u D n, u.user = v.user ∧ n ≤ t+(6*(B.size+M.size+P.size)+19+((218*(P*(M*B))+1)*13+8)) ∧
        Exec body ((embProg bank Empty.elim coordinate).seq finish) (mk v S) n (mk u D) ∧
        (∀ z, readAt blank (D.L (outer 1)) (D.R (outer 1)) (z-p) =
          RadixToBinary.binaryEncoding.encode (putWord source p (xs.map SparseRoleCircuit.encode) z)) ∧
        ∀ i, D.L (header i) = S.L (header i) ∧ D.R (header i) = S.R (header i) := by
  intro bank outer r header setup localRun finish w E t run user result src words empty
  have disjoint (i : Fin 13) (j : Fin T) : outer i ≠ bank j := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = 13+j.val at h
    omega
  have role : r 0 = bank io := by
    change Equiv.swap (outer 0) (bank io) (outer ((0 : Fin 10).castAdd 3)) = _
    rw [show (0 : Fin 10).castAdd 3 = (0 : Fin 13) by decide,Equiv.swap_apply_left]
  have other (i : Fin 10) (hi : i ≠ 0) : r i = outer (i.castAdd 3) := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact outer.injective.ne (fun eq => hi (Fin.ext (congrArg (fun j : Fin 13 => j.val) eq)))
    · exact disjoint _ _
  have apart (i : Fin 3) (j : Fin 10) : header i ≠ r j := by
    by_cases h : j = 0
    · subst j; rw [role]; exact disjoint _ _
    · rw [other _ h]
      apply outer.injective.ne
      intro eq
      have h := congrArg Fin.val eq
      change 10+i.val = j.val at h
      omega
  obtain ⟨y,_,hy,placed⟩ := exec_emb_ovr bank.injective (body' := body) (ι := Empty.elim)
    (fun e => nomatch e) run v rfl S rfl
  let I := embOvr bank E.get S
  have saved (i : Fin 13) := embOvr_off E.get S (fun j => (disjoint i j).symm)
  have eq := embStk_ovr bank.injective E S
  obtain ⟨u,D,n,hu,time,ret,out,frame⟩ := stagedLeafReturn_exec hP hM hB capacity body r header apart y I source p xs hx
    (by rw [role]; rw [← eq] at result; exact result)
    (by rw [other 1 (by decide),show (1 : Fin 10).castAdd 3 = (1 : Fin 13) by decide]; simpa only [I,(saved 1).1,(saved 1).2] using src)
    (by intro i; exact (saved _).2.trans (words i))
    (by intro i hi; rw [other _ (by intro h; subst i; contradiction)]
        exact ⟨(saved _).1.trans (empty i hi).1,(saved _).2.trans (empty i hi).2⟩)
  rw [other 1 (by decide),show (1 : Fin 10).castAdd 3 = (1 : Fin 13) by decide] at out
  refine ⟨u,D,t+n,hu.trans (hy.trans user),Nat.add_le_add_left time _,Exec.seq placed ret,out,?_⟩
  intro i
  have f := frame _ (fun j => (apart i j).symm)
  exact ⟨f.1.trans (saved _).1,f.2.trans (saved _).2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
