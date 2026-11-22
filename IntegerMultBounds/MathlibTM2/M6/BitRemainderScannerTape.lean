module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderStagedExchange

/-! Pass the rotated owner tape into the one-owner scanner and recover its result. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Stack Host
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (role)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem sameWordAtZero {m n : ℕ} {f : Fin m → ZMod 2} {g : Fin n → ZMod 2}
    (word : List.ofFn f = List.ofFn g) {L R} (live : WordAtZero f L R) : WordAtZero g L R := by
  intro z
  rw [live]
  have h := congrArg (List.map (SparseRoleCircuit.encode (a := prime))) word
  simp only [List.map_ofFn,Function.comp_def] at h
  rw [h]

/-- Adapt the scanner's native bank dimensions without copying the payload.
The entry and exit hypotheses use exactly the owner representations of the chart round trip. -/
theorem stagedScannerTape_exec {w B W T Q : ℕ} {P U : Type} {interval parent c}
    (body : P → Pr P T Q prime U) (code : Pr P T Q prime U)
    (port : Fin T) (u : HS T Q prime U) (S : Stacks T prime) (post : HS T Q prime U → Stacks T prime → ℕ → Prop) :
    let M := prime^(w+1)
    let layout := stagedScannerLayout w B W
    let R := LabelMask.records (role layout 142080)
    let nativeWidth := M^128*(layout.between*layout.afterD)
    let g := ordinaryIdentityRow (w+1)
    ∀ (x : Fin 142081 → Fin (M^16*(B*(M^112*W))) → ZMod 2) i,
    WordAtZero (fun j => singleLabelBank (firstRowLabel (w+1)) x i
      ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)) (S.L port) (S.R port) →
    (∀ words : Fin 1 → Fin (R*nativeWidth) → ZMod 2,
      RepT (phaseOwners words) (fun _ => S.L port) (fun _ => S.R port) →
      ∃ v F t, ∃ final : Fin 1 → Fin (R*nativeWidth) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧ post v F t ∧
        RepT (phaseOwners final) (fun _ => F.L port) (fun _ => F.R port) ∧
        OriginalPortReads R (layout.between*layout.afterD) (layout.beforeRows*1*B)
          interval parent c (words 0) (final 0)) →
    ∃ v F t, ∃ input output : Fin ((B*M^(64*64))*(M^128*W)) → ZMod 2,
      Exec body code (mk u S) t (mk v F) ∧ post v F t ∧ WordAtZero output (F.L port) (F.R port) ∧
      OriginalPortReads (B*M^(64*64)) W B interval parent c input output ∧
      ∀ b j a k, input (finProdFinEquiv (finProdFinEquiv (b,j),
        (finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W))) =
        if j = LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
        then x i (finProdFinEquiv (a,finProdFinEquiv (b,k))) else 0 := by
  intro M layout R nativeWidth g x i live scan
  obtain ⟨initial,entry,cells⟩ := identityScannerInput (w := w+1) x i _ _ live
  have size : R*nativeWidth = B*M^(64*64)*(M^128*W) := by
    simp [R,nativeWidth,layout,stagedScannerLayout,role,LabelMask.records,M]
  let native := fun j : Fin (R*nativeWidth) => initial (j.cast size)
  have sameWord : List.ofFn native = List.ofFn initial := by
    have castWord {m n : ℕ} (h : m = n) (f : Fin n → ZMod 2) :
        List.ofFn (fun j => f (j.cast h)) = List.ofFn f := by subst n; rfl
    exact castWord size initial
  have src := sameWordAtZero sameWord.symm entry
  obtain ⟨v,F,t,final,run,rest,ready,reads⟩ := scan (fun _ => native) (by
    intro j z
    exact (src z).symm.trans (congrArg (readAt blank (S.L port) (S.R port)) (sub_zero z).symm))
  obtain ⟨input,output,first,last,action⟩ := stagedScanner_reads (w := w) (B := B) (W := W) native (final 0) reads
  have out : WordAtZero (final 0) (F.L port) (F.R port) := by
    intro z
    have h := (ready 0 z).symm
    change readAt blank (F.L port) (F.R port) (z-0) = _ at h
    rw [sub_zero] at h
    exact h
  have eq : input = initial := List.ofFn_injective (first.trans sameWord)
  exact ⟨v,F,t,input,output,run,rest,sameWordAtZero last.symm out,action,eq ▸ cells⟩

/-- Compose the three host executions on the same tape. The native scanner's
time is charged once, and its cell contract determines the staged result. -/
theorem ordinaryOwner_exchange_exec {w B W T Q : ℕ} {P U : Type} {interval parent c}
    (body : P → Pr P T Q prime U) (enter scan leave : Pr P T Q prime U)
    (port dst : Fin T) (u : HS T Q prime U) (S : Stacks T prime)
    (units : ∀ i, IsUnit (parent i)) :
    let M := prime^(w+1)
    let A := M^16
    let K := M^112*W
    let V := B*(M^(64*64)*(M^128*W))
    let layout := stagedScannerLayout w B W
    let R := LabelMask.records (role layout 142080)
    let nativeWidth := M^128*(layout.between*layout.afterD)
    let g := ordinaryIdentityRow (w+1)
    let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
    ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i
      (v : HS T Q prime U) D t (budget : ℝ),
    Exec body enter (mk u S) t (mk v D) → t ≤ 22944*V+583 → v.user = u.user →
    WordAtZero (fun j => singleLabelBank (firstRowLabel (w+1)) x i
      ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)) (D.L port) (D.R port) →
    ∀ (ready : Stacks T prime → Prop),
    (∀ words : Fin 1 → Fin (R*nativeWidth) → ZMod 2,
      RepT (phaseOwners words) (fun _ => D.L port) (fun _ => D.R port) →
      ∃ z F n, ∃ final : Fin 1 → Fin (R*nativeWidth) → ZMod 2,
        Exec body scan (mk v D) n (mk z F) ∧ (z.user = v.user ∧ (n : ℝ) ≤ budget ∧ ready F) ∧
        RepT (phaseOwners final) (fun _ => F.L port) (fun _ => F.R port) ∧
        OriginalPortReads R (layout.between*layout.afterD) (layout.beforeRows*1*B)
          interval parent c (words 0) (final 0)) →
    (∀ (z : HS T Q prime U) F (input output : Fin ((B*M^(64*64))*(M^128*W)) → ZMod 2), ready F →
      WordAtZero output (F.L port) (F.R port) → OriginalPortReads (B*M^(64*64)) W B interval parent c input output →
      (∀ b j k, j ≠ idRow → input (finProdFinEquiv (finProdFinEquiv (b,j),k)) = 0) →
      ∃ v' E n, ∃ staged : Fin (A*(B*K)) → ZMod 2, Exec body leave (mk z F) n (mk v' E) ∧
        n ≤ 22982*V+599 ∧ v'.user = z.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (E.L dst) (E.R dst) ∧
        ∀ a b k, staged (finProdFinEquiv (a,finProdFinEquiv (b,k))) = output (finProdFinEquiv
          (finProdFinEquiv (b,idRow),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) →
    ∃ z F n, ∃ staged : Fin (A*(B*K)) → ZMod 2, Exec body (enter.seq (scan.seq leave)) (mk u S) n (mk z F) ∧
      (n : ℝ) ≤ budget+45926*V+1182 ∧ z.user = u.user ∧
      WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L dst) (F.R dst) ∧
      let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
      let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k) := by
  intro M A K V layout R nativeWidth g idRow x i v D t budget forward time user live ready execute restore
  obtain ⟨z,F,n,input,output,run,⟨same,paid,free⟩,out,reads,cells⟩ :=
    stagedScannerTape_exec body scan port v D (fun z F n => z.user = v.user ∧ (n : ℝ) ≤ budget ∧ ready F) x i live execute
  obtain ⟨v',E,k,staged,back,fee,saved,word,action⟩ := restore z F input output free out reads (by
    intro b j k hj
    obtain ⟨small,h⟩ := (finCongr (ordinaryCompact_width M W)).surjective k
    obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective small
    change (finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W) = _ at h
    rw [← h,cells,ite_eq_right hj])
  refine ⟨v',E,_,staged,Exec.seq forward (Exec.seq run back),?_,saved.trans (same.trans user),word,
    reads.stagedExchange input output (x i) staged units cells action⟩
  push_cast
  have ht : (t : ℝ) ≤ 22944*V+583 := by exact_mod_cast time
  have hk : (k : ℝ) ≤ 22982*V+599 := by exact_mod_cast fee
  linarith

end IntegerMultBounds.MathlibTM2.M6.BitNode
