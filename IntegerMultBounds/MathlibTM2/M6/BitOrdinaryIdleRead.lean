module

public import IntegerMultBounds.MathlibTM2.M6.BitChildCorrection
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledChildQueue
public import IntegerMultBounds.MathlibTM2.Cover.LabelCallerHeaders
public import IntegerMultBounds.MathlibTM2.Host.UnaryBinaryHalving
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece

/-! Interpret the ordinary PR589 owner tapes at a common live label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Matrix
open Shared50ModularControl (prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open Cover LabelTraversal FlatCoordinateLayout

open Stack Host

/-- The correction uses precisely the diagonal-pair part of a signed residual.
Its binary headers therefore give the same uniform per-volume swap bound. -/
theorem childCorrectionTime_le [M8.Machine.Net] (U : Type) :
    ∃ fixed swaps : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      ((List.finRange 127).map (fun i => Fallback.pairScalingTime U i.succ 0 i.succ w W M.size W.size)).sum+1 ≤
        (fixed+swaps*Fallback.swapVolumeRate w)*(M^128*W) := by
  obtain ⟨fixed,swaps,bound⟩ := Fallback.exceptionalRecordTime_binary_le U 127 0 0 0
  refine ⟨fixed,swaps,?_⟩
  intro w W positive M
  have full := bound (fun _ => 0) false w W 0 positive
  simp only [Nat.mul_zero,Nat.add_zero] at full
  apply le_trans _ full
  dsimp only [Fallback.exceptionalRecordTime,Fallback.exceptionalBodyTime,Fallback.signedResidualTime,M]
  omega

theorem childCorrectionTime_rate [M8.Machine.Net] (U : Type) :
    ∃ rate : ℝ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let time := ((List.finRange 127).map (fun i => Fallback.pairScalingTime U i.succ 0 i.succ w W M.size W.size)).sum+1
      (time : ℝ) ≤ rate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(M^128*W : ℕ) := by
  obtain ⟨fixed,swaps,bound⟩ := childCorrectionTime_le U
  refine ⟨fixed+(swaps : ℝ)*(3808275+M8.RevMachine.LeafCore.C),?_⟩
  intro w W positive M time
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have fee : ((fixed+swaps*Fallback.swapVolumeRate w : ℕ) : ℝ) ≤
      (fixed+(swaps : ℝ)*(3808275+M8.RevMachine.LeafCore.C))*power := by
    rw [Nat.cast_add,Nat.cast_mul,add_mul,mul_assoc]
    apply add_le_add _ (mul_le_mul_of_nonneg_left (Fallback.swapVolumeRate_le w) (Nat.cast_nonneg _))
    simpa using mul_le_mul_of_nonneg_left one (Nat.cast_nonneg fixed)
  exact (show (time : ℝ) ≤ ((fixed+swaps*Fallback.swapVolumeRate w : ℕ) : ℝ)*(M^128*W : ℕ) by
    exact_mod_cast bound w W positive).trans (mul_le_mul_of_nonneg_right fee (Nat.cast_nonneg _))

/-- Preparing the diagonal is linear in the binary modulus width and hence
fits in one row-volume charge even for a single spectator. -/
theorem childCorrectionSetup_volume_le (w W : ℕ) (positive : 0 < W) :
    let M := prime^(w+1)
    let H := M.size
    4*H+4+(128*(128*(8*(64*H)+14*H+22)+1)+1+(2*H+2)) + 1 + (128*128*(4*H+4)+1) ≤
      (128*(128*(8*64+14+22+8)+1)+15)*(M^128*W) := by
  intro M H
  have modulus : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have digits : H ≤ M^128*W := (Nat.size_le.mpr Nat.lt_two_pow_self : M.size ≤ M).trans
    ((show M ≤ M^128 by simpa using Nat.pow_le_pow_right modulus (by decide : 1 ≤ 128)).trans
      (Nat.le_mul_of_pos_right _ positive))
  have volume : 0 < M^128*W := Nat.mul_pos (pow_pos modulus _) positive
  omega

/-- Finish a nonroot scanner bank after the child queue transfer. The seven
header sources and two work registers can stay outside the caller/scan bank. -/
theorem childQueue_headers_exec {T Q w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin (21+59) ↪ Fin T) (source : Fin 7 → Fin T) (tmp aux : Fin T)
    (W a b h width : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (tail queue : List (Fin (prime+4)))
    (u v : HS T Q prime U) (S : Stacks T prime) (p : Pr P T Q prime U) (t : ℕ) :
    let scanner := (Fin.natAddEmb 21 (m := 59)).trans bank
    let dst := ordinaryHeaderPorts.trans scanner
    let words := ordinaryEntryWords W a b h false parent width queue
    let D : Stacks T prime := {S with R := (Function.update (Function.update (Function.update
      S.R (bank 7) tail) (scanner 58) queue) (scanner 47) (List.replicate width Node.tick))}
    Exec body p (mk u S) t (mk v D) → v.user = u.user →
    (∀ j, S.R (scanner j) = []) → (∀ i, S.R (source i) = words (ordinaryHeaderPorts i).val) →
    (∀ k ∈ tmp :: aux :: (List.finRange 7).map source, ∀ j, k ≠ bank j) →
    (∀ i, [source i,dst i,tmp,aux].Nodup) → S.R tmp = [] → S.R aux = [] →
    ∃ z F, z.user = u.user ∧ F.L = S.L ∧ (∀ j : Fin 59, F.R (scanner j) = words j.val) ∧
      Exec body (p.seq (Cover.Fallback.Record.copyLeafHeaders source dst tmp aux (List.finRange 7)))
        (mk u S) (t+(((List.finRange 7).map (fun i => 6*(words (ordinaryHeaderPorts i).val).length+6)).sum+1)) (mk z F) := by
  intro scanner dst words D prior same fresh sources outside ports temp auxFree
  have keep (k : Fin T) (hk : k ∈ tmp :: aux :: (List.finRange 7).map source) : D.R k = S.R k := by
    simp [D,scanner,Function.update_of_ne,outside k hk]
  have mem (i : Fin 7) : source i ∈ tmp :: aux :: (List.finRange 7).map source :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_finRange i)))
  obtain ⟨z,F,user,run,left,loaded,_⟩ := ordinaryHeaders_exec body source scanner (by decide) tmp aux
    W a b h false parent width queue v D (fun i => (keep _ (mem i)).trans (sources i))
    (fun i j => outside _ (mem i) _) ports ((keep _ (by simp)).trans temp)
    ((keep _ (by simp)).trans auxFree) (childQueue_scanner bank S tail queue width fresh)
  exact ⟨z,F,user.trans same,left,loaded,Exec.seq prior run⟩

/-- Normalize the caller's chart headers and decode the three row dimensions
and both spectator factors for the scanner. -/
theorem ordinaryDirectoryHeaders_exec {K T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 26 ↪ Fin T) (roles : Tapes K prime) (v : RecursiveInterchangeLayout.Descriptor) (w : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) (headers : LabelCallerHeaders.Represents r S roles v w) :
    let dims : List (Fin 7) := [0,1,2,4,5]
    (∀ i ∈ dims, S.R (LabelDecode.target r i) = []) → (∀ k ∈ [r 9,r 10,r 11], S.R k = []) →
    ∃ z F t, Exec body ((LabelCallerHeaders.load r).seq (LabelDecode.program r dims)) (mk u S) t (mk z F) ∧
      z.user = u.user ∧ t ≤ LabelCallerHeaders.cost r S + 17*(v.beforeRows+v.rows+v.beforeH+v.between+v.afterD)+86 ∧
      (∀ i ∈ dims, F.R (LabelDecode.target r i) = List.replicate (LabelDecode.field v w i) (bitSymbol true)) ∧
      (∀ i, F.R (LabelDecode.source r i) = (FlatCoordinateSchedule.bits (LabelDecode.field v w i)).map bitSymbol ∧
        F.L (LabelDecode.source r i) = [separator]) ∧
      ∀ j, j ∉ LabelCallerHeaders.ports r → j ∉ dims.map (LabelDecode.target r) → F.R j = S.R j ∧ F.L j = S.L j := by
  intro dims fresh scratch
  obtain ⟨a,B,m,user,paid,binary,off,load⟩ := LabelCallerHeaders.load_exec body r roles v w u S headers
  have separate (j : Fin 26) (small : j.val < 19) : r j ∉ LabelCallerHeaders.ports r := by
    intro mem
    obtain ⟨i,_,eq⟩ := List.mem_map.mp mem
    have val := congrArg Fin.val (r.injective eq)
    change 19+i.val = j.val at val
    omega
  obtain ⟨z,R,n,keep,time,unary,others,decode⟩ := LabelDecode.runs body r (LabelDecode.field v w)
    dims (by decide) a B (fun i _ => (binary i).1)
    (fun i hi => (off _ (separate _ (by change i.val < 19; omega))).1.trans (fresh i hi))
    (by
      intro j hj
      have unchanged : B.R j = S.R j := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl <;> exact (off _ (separate _ (by decide))).1
      exact unchanged.trans (scratch j hj))
  refine ⟨z,_,m+n,Exec.seq load decode,keep.trans user,?_,unary,?_,?_⟩
  · change n ≤ 17*(v.beforeRows+1)+(17*(v.rows+1)+(17*(v.beforeH+1)+(17*(v.between+1)+(17*(v.afterD+1)+0))))+1 at time
    omega
  · intro i
    refine ⟨(others _ ?_).trans (binary i).1,(binary i).2⟩
    intro mem
    obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
    have val := congrArg Fin.val (r.injective eq)
    change j.val = 19+i.val at val
    omega
  · intro j untouched unused
    exact ⟨(others j unused).trans (off j untouched).1,(off j untouched).2⟩

/-- From the normalized precision header, load the scanner's predecessor clock
on a fresh tape. Both the binary source and the scratch tapes are preserved. -/
theorem ordinaryClock_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    {src dst a b c : Fin T} (ports : [src,dst,a,b,c].Nodup) (w : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime)
    (word : S.R src = (FlatCoordinateSchedule.bits (w+1)).map bitSymbol)
    (empty : ∀ j ∈ [dst,a,b,c], S.R j = []) :
    ∃ z n, z.user = u.user ∧ n ≤ 17*w+35 ∧
      Exec body ((toUnary src dst a b c).seq (.act (.pop (.rt dst) (fun v _ => v) .done)))
        (mk u S) n (mk z {S with R := Function.update S.R dst (List.replicate w (bitSymbol true))}) := by
  obtain ⟨z,t,user,paid,decode⟩ := LabelDecode.field_exec body ports (w+1) u S word empty
  let D : Stacks T prime := {S with R := Function.update S.R dst (List.replicate (w+1) (bitSymbol true))}
  have pop := Exec.act (body := body) (.pop (.rt dst) (fun v _ => v) .done) (mk z D)
  have endPop : (Action.pop (.rt dst) (fun v _ => v) .done : Act T Q prime U).run (mk z D) =
      mk z {S with R := Function.update S.R dst (List.replicate w (bitSymbol true))} := by
    simp [Action.run,update_rt,D,Function.update_idem]
  rw [endPop] at pop
  exact ⟨z,t+1,user,by omega,Exec.seq decode pop⟩

/-- Multiply the decoded spectator factors and encode their product in the
minimal binary width expected on scanner tape 53. -/
theorem ordinarySpectatorWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (u : HS T Q prime U) (S : Stacks T prime) (between afterD : ℕ)
    (left : (S.R (r 0)).length = between) (right : (S.R (r 1)).length = afterD)
    (positive : 0 < afterD) (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (r j) = []) :
    let W := between*afterD
    ∃ z t, z.user = u.user ∧ t ≤ 34*W+14 ∧
      Exec body ((Mult.ShortConv.unaryProduct (r 0) (r 1) (r 2) (r 4) (r 5)).seq
        (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)))
        (mk u S) t (mk z {S with R := Function.update (Function.update S.R (r 2)
          (List.replicate W Node.tick)) (r 3) (binSyms W.size W)}) := by
  intro W
  obtain ⟨a,m,user,paid,product⟩ := Mult.ShortConv.unaryProduct_exec (body := body)
    (a := r 0) (b := r 1) (dst := r 2) (t₁ := r 4) (t₂ := r 5) (by simp) u S
    (empty 4 (by decide)) (empty 5 (by decide))
  rw [left,right,empty 2 (by decide),List.append_nil] at product
  let D : Stacks T prime := {S with R := Function.update S.R (r 2) (List.replicate W Node.tick)}
  have free (j : Fin 10) (hj : 3 ≤ j.val) : D.R (r j) = [] := by
    have ne : j ≠ 2 := fun eq => by subst j; exact (by decide : ¬3 ≤ (2 : Fin 10).val) hj
    change Function.update _ _ _ (r j) = _
    rw [Function.update_of_ne (r.injective.ne ne),empty j (by omega)]
  obtain ⟨z,n,keep,bill,binary⟩ := unaryBinary_exec (body := body) (src := r 2) (dst := r 3) (a := r 4)
    (h := r 5) (par := r 6) (bits := r 7) (cnt := r 8) (saved := r 9) (by simp) W a D
    (by simp [D]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact free _ (by decide))
  refine ⟨z,m+n,keep.trans user,?_,Exec.seq product binary⟩
  rw [left,right,show between*(4*afterD+9)+4 = 4*(between*afterD)+9*between+4 by ring] at paid
  have le : between ≤ W := Nat.le_mul_of_pos_right _ positive
  dsimp only [W] at *
  omega

/-- Generate the scanner modulus from the normalized binary precision header.
The program writes its own unit seed before exponentiation. -/
theorem ordinaryModulusWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 11 ↪ Fin T) (u : HS T Q prime U) (initial : Stacks T prime) (w : ℕ)
    (precision : initial.R (r 10) = (FlatCoordinateSchedule.bits (w+1)).map bitSymbol)
    (fresh : ∀ j : Fin 11, j.val ≤ 9 → initial.R (r j) = []) :
    let M := prime^(w+1)
    ∃ z n, z.user = u.user ∧ n ≤ 60*M+28 ∧
      let S : Stacks T prime := {initial with R := Function.update initial.R (r 0) [Node.tick]}
      Exec body ((Prog.act (.push (.rt (r 0)) (fun _ => Node.tick) .done)).seq ((toUnary (r 10) (r 1) (r 4) (r 5) (r 6)).seq
        ((Node.expProg 0 prime (r 0) (r 1) (r 2) (r 4) (r 5) (r 6)).seq
        (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)))))
        (mk u initial) n (mk z {S with R := Function.update (Function.update (Function.update S.R
          (r 1) (List.replicate (w+1) Node.tick)) (r 2) (List.replicate M Node.tick)) (r 3) (binSyms M.size M)}) := by
  intro M
  let S : Stacks T prime := {initial with R := Function.update initial.R (r 0) [Node.tick]}
  have seed := Exec.act (body := body) (.push (.rt (r 0)) (fun _ => Node.tick) .done) (mk u initial)
  have start : (Action.push (.rt (r 0)) (fun _ => Node.tick) .done : Act T Q prime U).run (mk u initial) =
      mk u S := by simp [Action.run,update_rt,S,fresh 0 (by decide)]
  rw [start] at seed
  have one : (S.R (r 0)).length = 1 := by simp [S]
  have empty (j : Fin 11) (lo : 1 ≤ j.val) (hi : j.val ≤ 9) : S.R (r j) = [] := by
    have ne : j ≠ 0 := fun eq => by subst j; exact (by decide : ¬1 ≤ (0 : Fin 11).val) lo
    exact (Function.update_of_ne (r.injective.ne ne) ..).trans (fresh j hi)
  obtain ⟨a,t,keep,price,decode⟩ := LabelDecode.field_exec body (src := r 10) (dst := r 1)
    (a := r 4) (b := r 5) (c := r 6) (by simp) (w+1) u S (by simpa [S] using precision) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact empty _ (by decide) (by decide))
  let D : Stacks T prime := {S with R := Function.update S.R (r 1) (List.replicate (w+1) Node.tick)}
  have free (j : Fin 11) (lo : 2 ≤ j.val) (hi : j.val ≤ 9) : D.R (r j) = [] := by
    have ne : j ≠ 1 := fun eq => by subst j; exact (by decide : ¬2 ≤ (1 : Fin 11).val) lo
    change Function.update _ _ _ (r j) = _
    rw [Function.update_of_ne (r.injective.ne ne),empty j (by omega) hi]
  obtain ⟨b,m,user,paid,power⟩ := LabelCounts.power_exec body (one := r 0) (exponent := r 1)
    (dst := r 2) (t₁ := r 4) (t₂ := r 5) (t₃ := r 6) (by simp) a D (by simpa [D] using one) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact free _ (by decide) (by decide))
  have exponent : (D.R (r 1)).length = w+1 := by simp [D]
  rw [exponent] at paid power
  let B : Stacks T prime := {D with R := Function.update D.R (r 2) (List.replicate M Node.tick)}
  have blank (j : Fin 11) (lo : 3 ≤ j.val) (hi : j.val ≤ 9) : B.R (r j) = [] := by
    have ne : j ≠ 2 := fun eq => by subst j; exact (by decide : ¬3 ≤ (2 : Fin 11).val) lo
    change Function.update _ _ _ (r j) = _
    rw [Function.update_of_ne (r.injective.ne ne),free j (by omega) hi]
  obtain ⟨z,l,last,bill,binary⟩ := unaryBinary_exec (body := body) (src := r 2) (dst := r 3) (a := r 4)
    (h := r 5) (par := r 6) (bits := r 7) (cnt := r 8) (saved := r 9) (by simp) M b B
    (by simp [B]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact blank _ (by decide) (by decide))
  refine ⟨z,1+(t+(m+l)),last.trans (user.trans keep),?_,Exec.seq seed (Exec.seq decode (Exec.seq power binary))⟩
  have size : w+1 ≤ M := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le
  change m ≤ 22*M at paid
  omega

/-- Place each local owner program on the same permanent owners and a
disjoint private bank, even when its local owner slots are scattered. -/
noncomputable def idlePassBank {owners n : ℕ} (width : Fin n → ℕ) (k : Fin n)
    (slots : Fin owners ↪ Fin (width k)) :=
  (returnChartBank slots (Function.Embedding.refl _)).trans (Fallback.Record.exchangeBank owners width k)

theorem idlePassBank_owner {owners n : ℕ} (width : Fin n → ℕ) (k : Fin n)
    (slots : Fin owners ↪ Fin (width k)) (i : Fin owners) :
    idlePassBank width k slots (slots i) = i.castAdd _ := by
  unfold idlePassBank
  rw [Function.Embedding.trans_apply,returnChartBank_selected,Fallback.Record.exchangeBank_shared]
  rfl

/-- Assemble the initial stacks, storing the common owners once. Unused
positions in the occurrence banks start blank. -/
noncomputable def idlePassStacks {owners n : ℕ} (width : Fin n → ℕ)
    (slots : ∀ k, Fin owners ↪ Fin (width k)) (shared : Stacks owners prime)
    (entry : ∀ k, Stacks (width k) prime) :
    Stacks (owners + Fintype.card (Σ j, Fin (width j))) prime := by
  let decode := (Fintype.equivFin (Σ j, Fin (width j))).symm
  classical
  let bank (common : Fin owners → List (Fin (prime+4))) (words : ∀ j, Fin (width j) → List (Fin (prime+4))) :
      Fin (owners + Fintype.card (Σ j, Fin (width j))) → List (Fin (prime+4)) :=
    Fin.addCases common fun i =>
      let a := decode i
      if ∃ t, slots a.1 t = a.2 then [] else words a.1 a.2
  exact ⟨shared.inp,shared.out,bank shared.L (fun j => (entry j).L),bank shared.R (fun j => (entry j).R)⟩

theorem idlePassStacks_view {owners n : ℕ} (width : Fin n → ℕ)
    (slots : ∀ k, Fin owners ↪ Fin (width k)) (shared : Stacks owners prime)
    (entry : ∀ k, Stacks (width k) prime) (k : Fin n)
    (common : embStk (slots k) (entry k) = shared) :
    embStk (idlePassBank width k (slots k)) (idlePassStacks width slots shared entry) = entry k := by
  subst shared
  apply Stacks.ext
  · rfl
  · rfl
  all_goals
    funext j
    by_cases used : ∃ i, slots k i = j
    · obtain ⟨i,rfl⟩ := used
      simp [embStk,Function.comp_apply,idlePassBank_owner,idlePassStacks]
    · have place : idlePassBank width k (slots k) j =
          Fin.natAdd owners (Fallback.Record.exchangeScratch width k j) := by
        unfold idlePassBank
        rw [Function.Embedding.trans_apply,returnChartBank_private _ _ j (fun i h => used ⟨i,h⟩),
          Fallback.Record.exchangeBank_private]
      have decode : (Fintype.equivFin (Σ a, Fin (width a))).symm (Fallback.Record.exchangeScratch width k j) =
          ⟨k,j⟩ := (Fintype.equivFin (Σ a, Fin (width a))).symm_apply_apply ⟨k,j⟩
      simp only [embStk,Function.comp_apply,place,idlePassStacks,Fin.addCases_right]
      rw [decode]
      simp [used]

/-- All local control states fit the maximum over the finite occurrence list. -/
theorem idlePass_fits {n : ℕ} (states : Fin n → ℕ) (k : Fin n) :
    states k ≤ Finset.univ.sup states := Finset.le_sup (Finset.mem_univ k)

/-- Recursive calls carry their occurrence index in the common procedure table. -/
noncomputable def idlePassBody {owners n : ℕ} {P U : Type} (width states : Fin n → ℕ)
    (positive : ∀ k, 0 < states k) (slots : ∀ k, Fin owners ↪ Fin (width k))
    (body : ∀ k, P → Pr P (width k) (states k) prime U) (f : Fin n × P) :
    Pr (Fin n × P) (owners + Fintype.card (Σ j, Fin (width j))) (Finset.univ.sup states) prime U :=
  statePlacedPr (idlePassBank width f.1 (slots f.1)) (idlePass_fits states f.1) (positive f.1)
    (Prod.mk f.1) (body f.1 f.2)

/-- One normalization step installs the local control state. The resulting run
preserves both stacks of every other occurrence's private tapes. -/
theorem idlePassBank_exec {owners n : ℕ} {P U : Type} (width states : Fin n → ℕ) (k : Fin n)
    (positive : ∀ j, 0 < states j) (slots : ∀ j, Fin owners ↪ Fin (width j))
    (body : ∀ j, P → Pr P (width j) (states j) prime U)
    (p : Pr P (width k) (states k) prime U) (v : HS _ (Finset.univ.sup states) prime U) (S : Stacks _ prime)
    (z : HS (width k) (states k) prime U) (D : Stacks (width k) prime) (t : ℕ) :
    let bank := idlePassBank width k (slots k)
    Exec (body k) p (mk (stateLiftDown (positive k) (embDn bank v)) (embStk bank S)) t (mk z D) →
    ∃ u F, Exec (idlePassBody width states positive slots body)
      (statePlacedNormalized bank (idlePass_fits states k) (positive k) (Prod.mk k) p)
      (mk v S) (1+t) (mk u F) ∧ u.user = z.user ∧ embStk bank F = D ∧
      ∀ j, j ≠ k → ∀ a : Fin (width j),
        let h := Fin.natAdd owners (Fallback.Record.exchangeScratch width j a)
        F.L h = S.L h ∧ F.R h = S.R h := by
  intro bank run
  obtain ⟨u,_,user,exec⟩ := statePlaced_exec_normalized bank bank.injective (idlePass_fits states k)
    (positive k) (Prod.mk k) (body' := idlePassBody width states positive slots body) (fun _ => rfl) v S run
  refine ⟨u,_,exec,user,embStk_ovr bank.injective _ _,fun j ne a => embOvr_off _ _ (fun b => ?_)⟩
  exact Fallback.Record.exchangeBank_avoids owners width (Ne.symm ne) _ a

/-- Sequence the physical passes on the idle's distinct owners. Each pass may
return a different representation of the tape bank and has its own time bound. -/
theorem idleCopies_exec {T Q : ℕ} {P U α : Type} (i : Fin 9)
    (body : P → Pr P T Q prime U) (program : (Fin 32 × Fin 5) × Fin 222 → Pr P T Q prime U)
    (budget : (Fin 32 × Fin 5) × Fin 222 → ℝ)
    (prepared : (Fin 32 × Fin 5) × Fin 222 → Stacks T prime → Prop)
    (ready : (Fin 142081 → α) → Stacks T prime → Prop)
    (effect : (Fin 32 × Fin 5) × Fin 222 → α → α → Prop)
    (pass : ∀ k x S (u : HS T Q prime U), ready x S → prepared k S →
      ∃ y D z n, Exec body (program k) (mk u S) n (mk z D) ∧ (n : ℝ) ≤ budget k ∧
        z.user = u.user ∧ ready y D ∧ (∀ a, a ≠ k → prepared a S → prepared a D) ∧
        effect k (x (idleTape i k)) (y (idleTape i k)) ∧
        ∀ j, j ≠ idleTape i k → y j = x j)
    (x : Fin 142081 → α) (S : Stacks T prime) (u : HS T Q prime U) (input : ready x S) (frames : ∀ k, prepared k S) :
    ∃ y D z n, Exec body (Prog.seqList (idleCopies.map program)) (mk u S) n (mk z D) ∧
      (n : ℝ) ≤ (idleCopies.map budget).sum + 1 ∧ z.user = u.user ∧ ready y D ∧
      (∀ k, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
      ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j := by
  have run (ks : List ((Fin 32 × Fin 5) × Fin 222)) (distinct : ks.Nodup)
      (x : Fin 142081 → α) (S : Stacks T prime) (u : HS T Q prime U) (input : ready x S) (frames : ∀ k ∈ ks, prepared k S) :
      ∃ y D z n, Exec body (Prog.seqList (ks.map program)) (mk u S) n (mk z D) ∧
        (n : ℝ) ≤ (ks.map budget).sum + 1 ∧ z.user = u.user ∧ ready y D ∧
        (∀ k ∈ ks, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
        ∀ j, (∀ k ∈ ks, j ≠ idleTape i k) → y j = x j := by
    induction ks generalizing x S u with
    | nil =>
      exact ⟨x,S,u,1,Exec.act .done _,by simp,rfl,input,by simp,fun _ _ => rfl⟩
    | cons k ks ih =>
      obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
      obtain ⟨v,B,t,m,firstRun,paid,keep,next,preserve,acted,off⟩ := pass k x S u input (frames k List.mem_cons_self)
      obtain ⟨y,D,z,n,rest,bill,user,final,acts,kept⟩ := ih tail v B t next
        (fun a ha => preserve a (fun h => fresh (h ▸ ha)) (frames a (List.mem_cons_of_mem _ ha)))
      refine ⟨y,D,z,m+n,Exec.seq firstRun rest,?_,user.trans keep,final,?_,?_⟩
      · simp only [List.map_cons,List.sum_cons,Nat.cast_add]
        linarith
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | member
        · rw [kept (idleTape i j) (fun a ha => (idleTape_injective i).ne (fun h => fresh (h.symm ▸ ha)))]
          exact acted
        · rw [← off _ ((idleTape_injective i).ne (fun h => fresh (h ▸ member)))]
          exact acts j member
      · intro j outside
        exact (kept j (fun a ha => outside a (List.mem_cons_of_mem _ ha))).trans
          (off j (outside k List.mem_cons_self))
  obtain ⟨y,D,z,n,exec,paid,user,final,acts,kept⟩ := run idleCopies
    (stageRuns_nodup.product (List.nodup_finRange _)) x S u input (fun k _ => frames k)
  refine ⟨y,D,z,n,exec,paid,user,final,fun k => acts k ?_,fun j h => kept j (fun a _ => h a)⟩
  exact List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩

/-- Physical cell of a rational address in the fixed block, label and spectator slice. -/
noncomputable def ordinaryRoleAddress {w R W parents : ℕ} (parent : Fin 64 → ZMod (prime^(w+1)))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1))
    (count : parents*(prime^(w+1))^(64*64) = R) (spectator : Fin W) :
    (Axis ⊕ Axis → ℚ) → Fin (R*((prime^(w+1))^128*W)) :=
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let axes := Equiv.sumCongr stageAxis.symm stageAxis.symm
    let frame := fromBlocks (diagonal parent*g) 0 0 (M8.ReversedExchange.rev 64*g)
    let row : Fin R := (finProdFinEquiv (block,LabelAddress.address g)).cast count
    let pack := fun x => finProdFinEquiv (row,index ((frame.mulVec (x ∘ axes)) ∘ finSumFinEquiv.symm) spectator)
    pack ∘ addressMod M

/-- All selected owners realize the compiled idle at the same packed address
for each live label, inherited block and spectator. -/
theorem ordinaryIdle_read {w R W parents : ℕ} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1)) (live : IsUnit g)
    (count : parents*(prime^(w+1))^(64*64) = R) (spectator : Fin W)
    (before after : Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2)
    (reads : ∀ k, OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val)
      (before (idleTape i k)) (after (idleTape i k)))
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → after j = before j) :
    let address := ordinaryRoleAddress parent block g count spectator
    readRoles address after = (Piece.remainder i.val).run (readRoles address before) := by
  dsimp only [ordinaryRoleAddress]
  apply idleCopies_modular_read (w+1) i _ before after _ off
  intro k e P x
  rw [idleExchange_axes _ (port_checked _ (idleRole i k).port.isLt) e.1 e.2]
  exact (reads k).exchange units block g live count (x ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) spectator

/-- Run the installed passes on their common bank and read the compiled idle
from the very same final store and summed step bound. -/
theorem ordinaryIdle_exec {w R W parents T Q : ℕ} {P U : Type} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (count : parents*(prime^(w+1))^(64*64) = R)
    (body : P → Pr P T Q prime U) (program : (Fin 32 × Fin 5) × Fin 222 → Pr P T Q prime U)
    (budget : (Fin 32 × Fin 5) × Fin 222 → ℝ)
    (prepared : (Fin 32 × Fin 5) × Fin 222 → Stacks T prime → Prop)
    (ready : (Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2) → Stacks T prime → Prop)
    (pass : ∀ k x S (u : HS T Q prime U), ready x S → prepared k S →
      ∃ y D z n, Exec body (program k) (mk u S) n (mk z D) ∧ (n : ℝ) ≤ budget k ∧
        z.user = u.user ∧ ready y D ∧ (∀ a, a ≠ k → prepared a S → prepared a D) ∧
        OriginalPortReads R W parents (idleInterval i k.2) parent
          (port (idleRole i k).port.val) (x (idleTape i k)) (y (idleTape i k)) ∧
        ∀ j, j ≠ idleTape i k → y j = x j)
    (x S u) (input : ready x S) (frames : ∀ k, prepared k S) :
    ∃ y D z n, Exec body (Prog.seqList (idleCopies.map program)) (mk u S) n (mk z D) ∧
      (n : ℝ) ≤ (idleCopies.map budget).sum + 1 ∧ z.user = u.user ∧ ready y D ∧
      (∀ j, (∀ k, j ≠ idleTape i k) → y j = x j) ∧
      ∀ block g, IsUnit g → ∀ spectator, let address := ordinaryRoleAddress parent block g count spectator
        readRoles address y = (Piece.remainder i.val).run (readRoles address x) := by
  obtain ⟨y,D,z,n,exec,paid,user,final,acts,kept⟩ := idleCopies_exec i body program budget prepared ready
    (fun k => OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val))
    pass x S u input frames
  exact ⟨y,D,z,n,exec,paid,user,final,kept,fun block g live spectator =>
    ordinaryIdle_read i parent units block g live count spectator x y acts kept⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
