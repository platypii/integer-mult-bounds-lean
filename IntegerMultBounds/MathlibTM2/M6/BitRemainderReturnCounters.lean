module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOutputPadding
public import IntegerMultBounds.MathlibTM2.Host.EmitRun

/-! Construct the return transpose's unary clocks from the two retained binary widths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem returnCounters_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (recordSize rowSize : Fin T)
    (apart : ∀ i, recordSize ≠ bank i ∧ rowSize ≠ bank i) :
    ∃ code, ∀ A K (u : HS T Q prime U) (S : Stacks T prime),
      S.R recordSize = binSyms K.size K → S.R rowSize = binSyms (A*K).size (A*K) →
      (∀ i, S.R (bank i) = []) →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧
        t ≤ 19*(K+A*K)+16 ∧ v.user = u.user ∧ F.L = S.L ∧
        (∀ i, F.R (bank i) = (transposeStacks (embStk bank S) [] []
          (List.replicate A (List.replicate K (Node.tick (A := prime))).reverse).flatten
          (List.replicate K Node.tick) []).R i) ∧
        ∀ j, j ≠ bank 3 → j ≠ bank 4 → F.R j = S.R j := by
  let emit (src : Fin T) (i : Fin 8) : Pr P T Q prime U :=
    emitRun src (bank 0) (bank i) (bank 1) (bank 2) (bank 5) Node.tick
  refine ⟨(emit recordSize 4).seq (emit rowSize 3),?_⟩
  intro A K u S small large empty
  have ports (s : Fin T) (h : ∀ i, s ≠ bank i) (i : Fin 8) (hi : [0,i,1,2,5].Nodup) :
      [s,bank 0,bank i,bank 1,bank 2,bank 5].Nodup :=
    List.nodup_cons.mpr ⟨by simp [h],hi.map bank.injective⟩
  have free (r) (h : r ∈ [bank 0,bank 1,bank 2,bank 5]) : S.R r = [] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> exact empty _
  obtain ⟨v,n,user,paid,record⟩ := emitRun_exec (body := body)
    (ports recordSize (fun i => (apart i).1) 4 (by decide)) _ _ (Nat.lt_size_self K)
    Node.tick u S small free
  rw [empty 4,List.append_nil] at record
  let D := {S with R := Function.update S.R (bank 4) (List.replicate K Node.tick)}
  have fresh (i : Fin 8) (h : i ≠ 4) : D.R (bank i) = [] := by
    simp [D,Function.update_of_ne (bank.injective.ne h),empty]
  obtain ⟨z,m,same,bill,rowRun⟩ := emitRun_exec (body := body)
    (ports rowSize (fun i => (apart i).2) 3 (by decide)) _ _ (Nat.lt_size_self (A*K))
    Node.tick v D (by simp [D,Function.update_of_ne (apart 4).2,large]) (by
      intro r h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> exact fresh _ (by decide))
  rw [fresh 3 (by decide),List.append_nil] at rowRun
  refine ⟨z,_,_,Exec.seq record rowRun,?_,same.trans user,rfl,?_,?_⟩
  · have h₁ := Nat.size_le.mpr (Nat.lt_two_pow_self (n := K))
    have h₂ := Nat.size_le.mpr (Nat.lt_two_pow_self (n := A*K))
    omega
  · intro i
    fin_cases i <;> simp [D,transposeStacks,Function.update_apply,bank.injective.eq_iff,empty]
  · intro j h₃ h₄
    simp [D,Function.update_of_ne h₃,Function.update_of_ne h₄]

open Cover
open FlatCoordinateSchedule (bits)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem ordinaryReturn_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (bank : Fin 14 ↪ Fin T) (headers : Fin 4 → Fin T)
    (apart : ∀ i j, headers i ≠ bank j) (port : Fin 12 ↪ Fin T)
    (shared : port 0 = bank 11) (privatePorts : ∀ j, j ≠ 0 → ∀ i, bank i ≠ port j)
    (trans : Fin 8 ↪ Fin T) (separate : ∀ j, (∀ i, bank i ≠ trans j) ∧ (∀ i, port i ≠ trans j))
    (pad : Fin 12 ↪ Fin T) (readPort : pad 0 = trans 6)
    (privatePad : ∀ j, j ≠ 0 → (∀ i, bank i ≠ pad j) ∧ (∀ i, port i ≠ pad j) ∧ (∀ i, trans i ≠ pad j))
    (recordSize rowSize : Fin T) (sizesApart : ∀ i, recordSize ≠ trans i ∧ rowSize ≠ trans i)
    (headersApart : ∀ i j, headers i ≠ trans j) :
    ∃ code, ∀ {w B W : ℕ} {interval parent c}, 0 < B → 0 < W →
      let M := prime^(w+1)
      let N := M^(64*64)
      let K := M^128*W
      let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
      ∀ (input output : Fin ((B*N)*K) → ZMod 2),
      OriginalPortReads _ W B interval parent c input output → c.Checked → (∀ i, IsUnit (parent i)) →
      (∀ b j k, j ≠ idRow → input (finProdFinEquiv (finProdFinEquiv (b,j),k)) = 0) →
      ∀ u S, (∀ i z, readAt blank (S.L (headers i)) (S.R (headers i)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![K,N,(0-idRow).val,B] i)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L (bank j) = [] ∧ S.R (bank j) = []) →
      WordAtZero output (S.L (bank 10)) (S.R (bank 10)) →
      (∀ z, readAt blank (S.L (bank 11)) (S.R (bank 11)) z = blank) →
      CropCounters port B N K S →
      (∀ z, readAt blank (S.L (port 1)) (S.R (port 1)) z = blank) →
      S.R recordSize = binSyms (M^112*W).size (M^112*W) →
      S.R rowSize = binSyms K.size K →
      (∀ i, S.R (trans i) = []) → S.L (trans 1) = [] →
      S.L (trans 6) = [] →
      CropCounters pad (M^16*B) (prime^(64*((w+1)*64))) (M^112*W) S →
      (∀ z, readAt blank (S.L (pad 1)) (S.R (pad 1)) z = blank) →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧ t ≤ 22982*(B*(N*K))+599 ∧ v.user = u.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L (pad 1)) (F.R (pad 1)) ∧
        (∀ (a : Fin (M^16)) (b : Fin B) (k : Fin (M^112*W)),
          staged (finProdFinEquiv (a,finProdFinEquiv (b,k))) = output (finProdFinEquiv
            (finProdFinEquiv (b,idRow),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) ∧
        ∀ j, (∀ i, bank i ≠ j) → (∀ i, port i ≠ j) → (∀ i, trans i ≠ j) → (∀ i, pad i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨setup,prepare⟩ := returnCounters_exec body trans recordSize rowSize sizesApart
  obtain ⟨back,run⟩ := ordinaryOutputPadded_exec body fits bank headers apart port shared privatePorts trans separate
    pad readPort privatePad
  refine ⟨setup.seq back,?_⟩
  intro w B W interval parent c hb hw M N K idRow input output reads checked units support u S words free src dest counters blankDest small large empty tmp left padCounters padBlank
  have dim : M^16*(M^112*W) = K := ordinaryCompact_width M W
  obtain ⟨v,D,n,setup,cost,user,same,ready,off⟩ := prepare (M^16) (M^112*W) u S small (dim ▸ large) empty
  have rot i := off (bank i) ((separate 3).1 i) ((separate 4).1 i)
  have crop i := off (port i) ((separate 3).2 i) ((separate 4).2 i)
  have padOff j (h : j ≠ 0) := off (pad j) ((privatePad j h).2.2 3).symm ((privatePad j h).2.2 4).symm
  obtain ⟨z,F,t,staged,ret,paid,saved,result,cells,frame⟩ := run hb hw input output reads checked units support v D
    (fun i l => by rw [same,off _ (headersApart i 3) (headersApart i 4)]; exact words i l)
    (fun j hs hd => by rw [same,rot]; exact free j hs hd)
    (by rw [same,rot]; exact src) (by rw [same,rot]; exact dest)
    (fun j hs hd l => by rw [same,crop]; exact counters j hs hd l)
    (by rw [same,crop]; exact blankDest)
    (List.replicate (M^112*W) Node.tick) [] (by simp only [List.length_replicate]; rfl) (same ▸ tmp) ready (same ▸ left)
    (fun j hs hd l => by rw [same,padOff j hs]; exact padCounters j hs hd l)
    (by rw [same,padOff 1 (by decide)]; exact padBlank)
  have hm : 0 < M := pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _
  have smaller : M^112*W ≤ K := dim ▸ Nat.le_mul_of_pos_left _ (pow_pos hm 16)
  have all : K ≤ B*(N*K) := (Nat.le_mul_of_pos_left _ (pow_pos hm (64*64))).trans
    (Nat.le_mul_of_pos_left _ hb)
  rw [dim] at cost
  change t ≤ 22944*(B*(N*K))+583 at paid
  refine ⟨z,F,_,staged,Exec.seq setup ret,by omega,saved.trans user,result,cells,?_⟩
  intro j h₁ h₂ h₃ h₄
  have untouched := frame j h₁ h₂ h₃ h₄
  exact ⟨untouched.1.trans (congrFun same j),untouched.2.trans (off j (h₃ 3).symm (h₃ 4).symm)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
