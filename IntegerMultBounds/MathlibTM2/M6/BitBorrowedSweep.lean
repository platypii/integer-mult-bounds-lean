module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedWindows

/-! Execute the packed PR589 stage from the unwrapped invocation workers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589

open Cover Certificates.PR589.Nine

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Action of the restored stage on active ports and inactive family spans,
at every independent matrix label. -/
def RestoredBorrowedStage (n : Fin 9) (w B K : ℕ)
    (x out : Fin 142081 → Fin ((prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  BorrowedPorts n w ((prime^w)^112*B) K x out ∧
  ∀ (ρ : Role) (inactive : ρ.bank.val / 2 ≠ BitHosting.activePair n.val)
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w),
  let row := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
      rw [← pow_mul]; congr 1; omega)
  let j := finProdFinEquiv (finProdFinEquiv (b,row),t)
  let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
  let read := fun word s => ext word (helperFieldCell (helperSlotField (port ρ.port.val) none w s) (0 : Fin 1) j)
  ∀ s, read (out tape) (M8.Exchange.exchange (Swap.Modular.reduce (prime^w) (familySum n ρ)) s) =
      read (x tape) s

theorem restoredBorrowedStage_of_trace {n w B K x y out}
    (trace : stageRuns.foldr (fun p next a => ∃ b, borrowedPackedStep n w B K p a b ∧ next b) (· = y) x)
    (restore : HelperLabelTrace w 1 (B*prime^(64*(w*64))*K) (restoreSlotChanges (stageFinalSlot n)) y out) :
    RestoredBorrowedStage n w B K x out := by
  refine ⟨?_,borrowedRestored_inactive trace restore⟩
  intro run t g cell owner j src dst read input
  have kept (i : Fin 661) (hi : i.val < 222) : read out i = read y i := by
    have fixed := restoredStage_activePort n run (⟨i.val,hi⟩ : Fin 222) restore
    change out (owner i) = y (owner i) at fixed
    funext state
    simpa only [read,phaseRead,Copy.extendStored,dite_eq_left i.isLt] using
      congrFun fixed (FlatCoordinateLayout.index (AffineFieldCoordinates.embed state) j)
  rw [kept src (by dsimp [src]; omega),kept dst (by dsimp [dst]; omega)]
  exact borrowedPacked_ports trace run t g cell

/-- Packing and restoration follow fixed schedules for the stage, independent
of the recursive workers' tapes, state budgets, and parent dimensions. -/
noncomputable def stagePackingRate [M8.Machine.Net] (n : Fin 9) : ℝ :=
  (stageRuns.map (borrowedPackRate n)).sum + helperChangesRate (restoreSlotChanges (stageFinalSlot n))

/-- Sequence all stage workers and restoration on a single physical archive.
Each unwrapped worker consumes its own private data and preserves later workers' data. -/
theorem archivedSweep_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type} (n : Fin 9)
    (fan : Fin (142081+2) ↪ Fin T) (capacity : columnCapacity ≤ Q) (body : P → Pr P T Q prime U)
    (w B K : ℕ) :
    let bank := Fin.castAddEmb 273 (n := T)
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := bank.trans scratch
    let full := (fan.trans bank).trans scratch
    let outer := fun f => embProg owner id (body f)
    let W := B*prime^(64*(w*64))*K
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    let scale := (V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
    0 < V → ∀ (saved : Fin 32 × Fin 5 → Stacks T prime → Prop) (price : Fin 32 × Fin 5 → ℝ),
    (∀ p, ∃ call, ∀ (S : Stacks T prime), saved p S →
      ∀ (a : Fin 142081 → Fin V → ZMod 2) v D, HelperFan fan a D →
      (∀ j, (∀ h, fan h ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
      ∃ z F m b, Exec body call (mk v D) m (mk z F) ∧ (m : ℝ) ≤ price p ∧ z.user = v.user ∧
        HelperFan fan b F ∧ BorrowedStep n w blocks K p a b ∧ ∀ j, j ≠ p → saved j S → saved j F) →
    ∃ code, ∀ x u S, HelperFan full x S →
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      (∀ j, saved j (embStk owner S)) →
      ∃ z F t out, Exec outer code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ (stageRuns.map (fun p => borrowedPackRate n p*scale+price p)).sum+
          helperChangesRate (restoreSlotChanges (stageFinalSlot n))*scale ∧
        z.user = u.user ∧ HelperFan full out F ∧ RestoredBorrowedStage n w B K x out := by
  intro bank scratch owner full outer W blocks V scale pos saved price calls
  let ready (S : Stacks ((T+273)+LeafCore.small) prime) :=
    (∀ i j, S.R (scratch (borrowedHeaders T i j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) ∧
    ∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []
  obtain ⟨code,run⟩ := borrowedSweep_exec (w := w) (B := B) (K := K) n outer full
    (fun j S => saved j (embStk owner S)) ready (fun p => borrowedPackRate n p*scale+price p)
    (helperChangesRate (restoreSlotChanges (stageFinalSlot n))*scale) (by
      intro p
      obtain ⟨call,invoke⟩ := calls p
      obtain ⟨pack,step⟩ := archivedBorrowedCall_host n p fan capacity body
      refine ⟨.seq pack (embProg owner id call),?_⟩
      intro x u S live guard fresh
      obtain ⟨z,F,t,y,exec,bill,user,done,act,keep,headers,clear⟩ := step w B K pos x u S call (price p)
        (fun F => ∀ j, j ≠ p → saved j (embStk owner S) → saved j F)
        guard.1 live guard.2 (invoke (embStk owner S) fresh)
      exact ⟨z,F,t,y,exec,bill,user,done,act,⟨fun i j => (headers i j).trans (guard.1 i j),clear⟩,keep⟩) (by
      obtain ⟨restore,finish⟩ := archivedBorrowedRestore_host n fan capacity outer
      refine ⟨restore,?_⟩
      intro x u S live guard
      obtain ⟨z,F,t,y,exec,bill,user,done,act,_,_⟩ := finish w B K pos x u S guard.1 live guard.2
      exact ⟨z,F,t,y,exec,bill,user,done,act⟩)
  refine ⟨code,?_⟩
  intro x u S live headers free fresh
  obtain ⟨z,F,t,y,out,exec,bill,user,done,steps,restore⟩ := run x u S live ⟨headers,free⟩ fresh
  exact ⟨z,F,t,out,exec,bill,user,done,restoredBorrowedStage_of_trace steps restore⟩

theorem archivedSweepWithCharge [M8.Machine.Net] {T Q : ℕ} {P U : Type} (n : Fin 9)
    (fan : Fin (142081+2) ↪ Fin T) (capacity : columnCapacity ≤ Q) (body : P → Pr P T Q prime U)
    :
    let bank := Fin.castAddEmb 273 (n := T)
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := bank.trans scratch
    let full := (fan.trans bank).trans scratch
    let outer := fun f => embProg owner id (body f)
    ∃ rate : ℝ, ∀ (call : Fin 32 × Fin 5 → Pr P T Q prime U), ∃ code, ∀ w B K : ℕ,
    let W := B*prime^(64*(w*64))*K
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    let scale := (V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
    0 < V → ∀ (saved : Fin 32 × Fin 5 → Stacks T prime → Prop) (price : Fin 32 × Fin 5 → ℕ),
    (∀ p, ∀ (S : Stacks T prime), saved p S →
      ∀ (a : Fin 142081 → Fin V → ZMod 2) v D, HelperFan fan a D →
      (∀ j, (∀ h, fan h ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
      ∃ z F m b, Exec body (call p) (mk v D) m (mk z F) ∧ (∀ js : List (Fin T), js.Nodup → m+tapeCharge (fun l r => 4*l.length+2*r.length+4) js F ≤
          tapeCharge (fun l r => 4*l.length+2*r.length+4) js D+price p) ∧ z.user = v.user ∧
        HelperFan fan b F ∧ BorrowedStep n w blocks K p a b ∧ ∀ j, j ≠ p → saved j S → saved j F) →
    ∀ x u S, HelperFan full x S →
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      (∀ j, saved j (embStk owner S)) →
      ∃ z F t out, Exec outer code (mk u S) t (mk z F) ∧
        (∀ js : List (Fin ((T+273)+LeafCore.small)), js.Nodup →
          (t : ℝ)+tapeCharge (fun l r => 4*l.length+2*r.length+4) js F ≤
            tapeCharge (fun l r => 4*l.length+2*r.length+4) js S+rate*scale+((stageRuns.map price).sum : ℕ)) ∧
        z.user = u.user ∧ HelperFan full out F ∧ RestoredBorrowedStage n w B K x out := by
  intro bank scratch owner full outer
  choose packRate pack step using fun p => archivedBorrowedCallWithCharge n p fan capacity body
  obtain ⟨restoreRate,restore,finish⟩ := archivedRestoreWithCharge n fan capacity outer
  refine ⟨(stageRuns.map packRate).sum+restoreRate,?_⟩
  intro call
  let placed := fun p => (pack p).seq (embProg owner id (call p))
  refine ⟨stageRuns.foldr (fun p tail => .seq (placed p) tail) restore,?_⟩
  intro w B K W blocks V scale pos saved price calls
  let weight := fun (l r : List (Fin (prime+4))) => 4*l.length+2*r.length+4
  let ready (S : Stacks ((T+273)+LeafCore.small) prime) :=
    (∀ i j, S.R (scratch (borrowedHeaders T i j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) ∧
    ∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []
  have run := borrowedSweepWithPotential (w := w) (B := B) (K := K) n
    (fun (js : {l : List (Fin ((T+273)+LeafCore.small)) // l.Nodup}) D => (tapeCharge weight js.val D : ℝ)) outer full
    (fun j S => saved j (embStk owner S)) ready (fun p => packRate p*scale+(price p : ℝ))
    (restoreRate*scale) placed restore (by
      intro p x u S live guard fresh
      obtain ⟨z,F,t,y,exec,bill,user,done,act,keep,headers,clear⟩ := step p w B K pos x u S (call p) (price p)
        (fun F => ∀ j, j ≠ p → saved j (embStk owner S) → saved j F)
        guard.1 live guard.2 (calls p (embStk owner S) fresh)
      exact ⟨z,F,t,y,exec,(fun js => by simpa only [← add_assoc] using bill js.val js.property),user,done,act,⟨fun i j => (headers i j).trans (guard.1 i j),clear⟩,keep⟩) (by
      intro x u S live guard
      obtain ⟨z,F,t,y,exec,bill,user,done,act,_,_⟩ := finish w B K pos x u S guard.1 live guard.2
      exact ⟨z,F,t,y,exec,(fun js => bill js.val js.property),user,done,act⟩)
  intro x u S live headers free fresh
  obtain ⟨z,F,t,y,out,exec,bill,user,done,steps,restore⟩ := run x u S live ⟨headers,free⟩ fresh
  refine ⟨z,F,t,out,exec,?_,user,done,restoredBorrowedStage_of_trace steps restore⟩
  intro js unique
  have h := bill ⟨js,unique⟩
  simp only [List.sum_map_add,List.sum_map_mul_right,← Nat.cast_list_sum,add_mul] at h ⊢
  have castSum (ls : List (Fin 32 × Fin 5)) : (ls.map fun p => (price p : ℝ)).sum = ((ls.map price).sum : ℕ) := by
    induction ls with
    | nil => simp
    | cons p ls ih => simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]
  rw [castSum] at h
  dsimp only [weight] at h
  linarith only [h]

private theorem archiveStageBill [M8.Machine.Net] (n : Fin 9)
    (coeff : Fin 32 × Fin 5 → ℝ) (childTime : ℕ → ℕ) (packScale callScale : ℝ) :
    let children := fun p => ((List.range' (stageChildStart n+runChildStart p)
      Geometry.Moves.localPaid.length).map childTime).sum
    (stageRuns.map (fun p => borrowedPackRate n p*packScale+(coeff p*callScale+(children p : ℝ)))).sum+
      helperChangesRate (restoreSlotChanges (stageFinalSlot n))*packScale =
      stagePackingRate n*packScale+(stageRuns.map coeff).sum*callScale+
        (((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum : ℕ) := by
  intro children
  have total := scheduledChildBill (fun _ => Geometry.Moves.localPaid) childTime stageRuns stageRuns_nodup (stageChildStart n)
  change (stageRuns.map children).sum = _ at total
  have castSum (ls : List (Fin 32 × Fin 5)) :
      (ls.map fun p => (children p : ℝ)).sum = ((ls.map children).sum : ℕ) := by
    induction ls with
    | nil => simp
    | cons p ls ih => simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]
  simp only [List.sum_map_add,List.sum_map_mul_right,castSum,total,stagePackingRate,add_mul]
  ring

/-- Allocate disjoint private tapes for the invocation workers and one archive
for the whole stage. Only the owner words are shared between worker banks. -/
theorem allocatedArchiveSweep_host [M8.Machine.Net] (n : Fin 9) :
    let J := Fin 32 × Fin 5
    ∀ (tapes : J → ℕ) (ports : ∀ p, Fin (142081+2) ↪ Fin (tapes p)),
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (banks : ∀ p, Fin (tapes p) ↪ Fin T),
    ∀ {P : J → Type} {U : Type} {Q : ℕ}, columnCapacity ≤ Q →
    ∀ (body : ∀ p, P p → Pr (P p) (tapes p) Q prime U) (w B K : ℕ),
    let blocks := (prime^w)^112*B
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    let scale := (V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := (Fin.castAddEmb 273 (n := T)).trans scratch
    let host := fun f : (p : J) × P p => embProg (banks f.1) (Sigma.mk f.1) (body f.1 f.2)
    let outer := fun f => embProg owner id (host f)
    0 < V → ∀ (coeff : J → ℝ) (childTime : ℕ → ℕ),
    (∀ p, SeededInvocation (w := w) (B := blocks) (K := K) n p (ports p) (body p) (coeff p) childTime) →
    ∀ shared : Stacks (142081+2) prime, ∃ initial : Stacks T prime, embStk fan initial = shared ∧
    ∃ code, ∀ x u S, HelperFan (fan.trans owner) x S →
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      (∀ j, (∀ h, fan h ≠ j) → S.L (owner j) = initial.L j ∧ S.R (owner j) = initial.R j) →
      ∃ z F t out, Exec outer code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ stagePackingRate n*scale+(stageRuns.map coeff).sum*(V*(w : ℝ)^M8.Machine.BudgetBound.tau)+
          (((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum : ℕ) ∧
        z.user = u.user ∧ HelperFan (fan.trans owner) out F ∧ RestoredBorrowedStage n w B K x out := by
  intro J tapes ports
  obtain ⟨T,fan,banks,select,_,prepare,apart⟩ := copyWindowBanks tapes ports
  refine ⟨T,fan,banks,?_⟩
  intro P U Q cap body w B K blocks W V scale scratch owner host outer pos coeff childTime supplied shared
  choose call ready using supplied
  choose seed _ runs using fun p => ready p shared
  obtain ⟨initial,owners,stored⟩ := prepare shared seed
  let saved (p : J) (S : Stacks T prime) := ∀ i, (∀ h, ports p h ≠ i) →
    S.L (banks p i) = (seed p).L i ∧ S.R (banks p i) = (seed p).R i
  have project p (S : Stacks T prime) : embStk (ports p) (embStk (banks p) S) = embStk fan S := by
    simp only [embStk,Function.comp_def,select]
  refine ⟨initial,owners,?_⟩
  obtain ⟨code,run⟩ := archivedSweep_exec n fan cap host w B K pos saved
    (fun p => coeff p*V*(w : ℝ)^M8.Machine.BudgetBound.tau+
      ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map childTime).sum) (by
      intro p
      refine ⟨embProg (banks p) (Sigma.mk p) (call p),?_⟩
      intro S ready a v D live held
      have privateAt j i (h : ∀ k, ports j k ≠ i) := held (banks j i) (apart j i h).1
      obtain ⟨z,F,m,b,exec,paid,user,done,act⟩ := runs p a (embDn (banks p) v) (embStk (banks p) D)
        (by simpa only [HelperFan,project] using live) (fun i h =>
          ⟨(privateAt p i h).1.trans (ready i h).1,(privateAt p i h).2.trans (ready i h).2⟩)
      obtain ⟨y,E,placed,_,same,view,off⟩ := exec_emb (ι := Sigma.mk p) (body' := host)
        (banks p).injective (fun _ => rfl) exec v rfl D rfl
      rw [← view] at done
      refine ⟨y,E,m,b,placed,paid,same.trans user,by simpa only [HelperFan,project] using done,act,?_⟩
      intro j ne valid i h
      obtain ⟨l,r⟩ := off _ ((apart j i h).2 p ne.symm)
      exact ⟨l.trans ((privateAt j i h).1.trans (valid i h).1),r.trans ((privateAt j i h).2.trans (valid i h).2)⟩)
  refine ⟨code,?_⟩
  intro x u S live headers free fresh
  obtain ⟨z,F,t,out,exec,bill,user,done,act⟩ := run x u S live headers free (by
    intro p i h
    have held := fresh _ (apart p i h).1
    exact ⟨held.1.trans (stored p i h).1,held.2.trans (stored p i h).2⟩)
  refine ⟨z,F,t,out,exec,?_,user,done,act⟩
  rw [← archiveStageBill n coeff childTime scale (V*(w : ℝ)^M8.Machine.BudgetBound.tau)]
  simpa only [scale,V,blocks,mul_assoc] using bill


/-- Allocate the borrowed sweep once. Only the private seeds and costs vary with the parent dimensions. -/
theorem allocatedArchiveSweepWithCharge [M8.Machine.Net] (n : Fin 9) :
    let J := Fin 32 × Fin 5
    ∀ (tapes : J → ℕ) (ports : ∀ p, Fin (142081+2) ↪ Fin (tapes p)),
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (banks : ∀ p, Fin (tapes p) ↪ Fin T),
    ∀ {P : J → Type} {U : Type} {Q : ℕ}, columnCapacity ≤ Q →
    ∀ (body : ∀ p, P p → Pr (P p) (tapes p) Q prime U),
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := (Fin.castAddEmb 273 (n := T)).trans scratch
    let host := fun f : (p : J) × P p => embProg (banks f.1) (Sigma.mk f.1) (body f.1 f.2)
    let outer := fun f => embProg owner id (host f)
    ∃ rate : ℝ, ∀ (call : ∀ p, Pr (P p) (tapes p) Q prime U), ∃ code, ∀ w B K : ℕ,
    let blocks := (prime^w)^112*B
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    let scale := (V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
    0 < V → ∀ (work : J → ℕ) (childTime : ℕ → ℕ),
    (∀ p (shared : Stacks (142081+2) prime), ∃ seed : Stacks (tapes p) prime, embStk (ports p) seed = shared ∧
      ∀ a v D, HelperFan (ports p) a D →
        (∀ j, (∀ h, ports p h ≠ j) → D.L j = seed.L j ∧ D.R j = seed.R j) →
        ∃ z F m b, Exec (body p) (call p) (mk v D) m (mk z F) ∧
          (∀ js : List (Fin (tapes p)), js.Nodup →
            m+tapeCharge (fun l r => 4*l.length+2*r.length+4) js F ≤
              tapeCharge (fun l r => 4*l.length+2*r.length+4) js D+(work p+
              ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map childTime).sum)) ∧
          z.user = v.user ∧ HelperFan (ports p) b F ∧ BorrowedStep n w blocks K p a b) →
    ∀ shared : Stacks (142081+2) prime, ∃ initial : Stacks T prime, embStk fan initial = shared ∧
    ∀ x u S, HelperFan (fan.trans owner) x S →
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      (∀ j, (∀ h, fan h ≠ j) → S.L (owner j) = initial.L j ∧ S.R (owner j) = initial.R j) →
      ∃ z F t out, Exec outer code (mk u S) t (mk z F) ∧
        (∀ js : List (Fin ((T+273)+LeafCore.small)), js.Nodup →
          (t : ℝ)+tapeCharge (fun l r => 4*l.length+2*r.length+4) js F ≤
          tapeCharge (fun l r => 4*l.length+2*r.length+4) js S+rate*scale+((stageRuns.map work).sum : ℕ)+
          (((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum : ℕ)) ∧
        z.user = u.user ∧ HelperFan (fan.trans owner) out F ∧ RestoredBorrowedStage n w B K x out := by
  intro J tapes ports
  obtain ⟨T,fan,banks,select,_,prepare,apart⟩ := copyWindowBanks tapes ports
  refine ⟨T,fan,banks,?_⟩
  intro P U Q cap body
  let host := fun f : (p : J) × P p => embProg (banks f.1) (Sigma.mk f.1) (body f.1 f.2)
  obtain ⟨rate,sweep⟩ := archivedSweepWithCharge n fan cap host
  intro scratch owner stageHost outer
  refine ⟨rate,?_⟩
  intro call
  obtain ⟨code,execute⟩ := sweep (fun p => embProg (banks p) (Sigma.mk p) (call p))
  refine ⟨code,?_⟩
  intro w B K blocks W V scale pos work childTime supplied shared
  choose seed _ runs using fun p => supplied p shared
  obtain ⟨initial,owners,stored⟩ := prepare shared seed
  let saved (p : J) (S : Stacks T prime) := ∀ i, (∀ h, ports p h ≠ i) →
    S.L (banks p i) = (seed p).L i ∧ S.R (banks p i) = (seed p).R i
  have project p (S : Stacks T prime) : embStk (ports p) (embStk (banks p) S) = embStk fan S := by
    simp only [embStk,Function.comp_def,select]
  refine ⟨initial,owners,?_⟩
  have run := execute w B K pos saved
    (fun p => work p+
      ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map childTime).sum) (by
      intro p S ready a v D live held
      have privateAt j i (h : ∀ k, ports j k ≠ i) := held (banks j i) (apart j i h).1
      obtain ⟨z,F,m,b,exec,paid,user,done,act⟩ := runs p a (embDn (banks p) v) (embStk (banks p) D)
        (by simpa only [HelperFan,project] using live) (fun i h =>
          ⟨(privateAt p i h).1.trans (ready i h).1,(privateAt p i h).2.trans (ready i h).2⟩)
      obtain ⟨y,E,placed,_,same,view,off⟩ := exec_emb (ι := Sigma.mk p) (body' := host)
        (banks p).injective (fun _ => rfl) exec v rfl D rfl
      rw [← view] at done paid
      refine ⟨y,E,m,b,placed,placedCleanup_cost_le (banks p) D E _ m _ off paid,same.trans user,by simpa only [HelperFan,project] using done,act,?_⟩
      intro j ne valid i h
      obtain ⟨l,r⟩ := off _ ((apart j i h).2 p ne.symm)
      exact ⟨l.trans ((privateAt j i h).1.trans (valid i h).1),r.trans ((privateAt j i h).2.trans (valid i h).2)⟩)
  intro x u S live headers free fresh
  obtain ⟨z,F,t,out,exec,bill,user,done,act⟩ := run x u S live headers free (by
    intro p i h
    have held := fresh _ (apart p i h).1
    exact ⟨held.1.trans (stored p i h).1,held.2.trans (stored p i h).2⟩)
  refine ⟨z,F,t,out,exec,?_,user,done,act⟩
  intro js unique
  have h := bill js unique
  have directory := scheduledChildBill (fun _ => Geometry.Moves.localPaid) childTime stageRuns stageRuns_nodup (stageChildStart n)
  simp only [List.sum_map_add] at h
  change (stageRuns.map (fun p => ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map childTime).sum)).sum = _ at directory
  rw [directory] at h
  simpa only [Nat.cast_add,add_assoc] using h

-- The earlier per-invocation header banks are available at c9d3ef47.

abbrev StageRun := Fin 32 × Fin 5
abbrev MoveIndex := Fin (Geometry.Moves.phaseEdges.filter positiveMove).length
abbrev CopyIndex := Fin Copy.lifecycles.length

def PackedStageExecution [M8.Machine.Net] {Q w B K : ℕ} {P U : Type} (n : Fin 9)
    (tapes : StageRun → ℕ) (body : ∀ p, P → Pr P (tapes p) Q prime U)
    (coeff : StageRun → ℝ) (required : (ℕ → ℕ) → Prop) : Prop :=
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ p, Fin (tapes p) ↪ Fin T),
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := (Fin.castAddEmb 273 (n := T)).trans scratch
    let worker := fun f : (_ : StageRun) × P => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    let host := fun f => embProg owner id (worker f)
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    ∀ childTime : ℕ → ℕ,
    required childTime →
    ∀ shared : Stacks (142081+2) prime, ∃ initial : Stacks T prime, embStk fan initial = shared ∧
    ∃ code, ∀ x u S, HelperFan (fan.trans owner) x S →
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) =
        (Routines.hdr (helperAdjacentView w 1 (B*prime^(64*(w*64))*K) i) j).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      (∀ i, (∀ h, fan h ≠ i) → S.L (owner i) = initial.L i ∧ S.R (owner i) = initial.R i) →
      ∃ z F t out, Exec host code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ (stagePackingRate n+(stageRuns.map coeff).sum)*(V*(w : ℝ)^M8.Machine.BudgetBound.tau) +
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum ∧
        z.user = u.user ∧ HelperFan (fan.trans owner) out F ∧ RestoredBorrowedStage n w B K x out

theorem helperFan_of_agree {k T V : ℕ} {fan : Fin (k+2) ↪ Fin T}
    {x : Fin k → Fin V → ZMod 2} {S F : Stacks T prime} (live : HelperFan fan x S)
    (agree : ∀ i, F.L (fan i) = S.L (fan i) ∧ F.R (fan i) = S.R (fan i)) : HelperFan fan x F := by
  intro i j
  change _ = readAt _ (F.L (fan i)) (F.R (fan i)) _
  rw [(agree i).1,(agree i).2]
  exact live i j

private theorem liftFanExecution {k T L V Q : ℕ} {P U : Type} (stage : Fin T ↪ Fin L)
    (fan : Fin (k+2) ↪ Fin T) (body : P → Pr P T Q prime U) (code : Pr P T Q prime U)
    (v : HS L Q prime U) (F : Stacks L prime) (price : ℝ)
    (effect : (Fin k → Fin V → ZMod 2) → Prop)
    (run : ∃ y D m out, Exec body code (mk (embDn stage v) (embStk stage F)) m (mk y D) ∧
      (m : ℝ) ≤ price ∧ y.user = v.user ∧ HelperFan fan out D ∧ effect out) :
    ∃ z G m, Exec (fun f => embProg stage id (body f)) (embProg stage id code) (mk v F) m (mk z G) ∧
      (m : ℝ) ≤ price ∧ z.user = v.user ∧ ∃ out, HelperFan (fan.trans stage) out G ∧ effect out := by
  obtain ⟨y,D,m,out,exec,paid,same,done,act⟩ := run
  obtain ⟨z,G,placed,_,user,view,_⟩ := exec_emb (ι := id) (body' := fun f => embProg stage id (body f))
    stage.injective (fun _ => rfl) exec v rfl F rfl
  rw [← view] at done
  exact ⟨z,G,m,placed,paid,user.trans same,out,done,act⟩

private theorem stageAfterSetup {T L Q V : ℕ} {P U : Type}
    (fan : Fin (142081+2) ↪ Fin T) (host : P → Pr P ((T+273)+L) Q prime U)
    (code : Pr P ((T+273)+L) Q prime U) (words : Fin 127 → Fin 6 → List (Fin (prime+4)))
    (initial : Stacks T prime) (price : ℝ) (effect : (Fin 142081 → Fin V → ZMod 2) → Prop)
    (x : Fin 142081 → Fin V → ZMod 2) :
    let stage := Fin.natAddEmb 80 (m := (T+273)+L)
    let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb L)
    let full := (fan.trans owner).trans stage
    ∀ S, HelperFan full x S →
    (∀ j : Fin L, S.L (stage (j.natAdd (T+273))) = [] ∧ S.R (stage (j.natAdd (T+273))) = []) →
    (∀ i, (∀ h, fan h ≠ i) → S.L (stage (owner i)) = initial.L i ∧ S.R (stage (owner i)) = initial.R i) →
    (∀ v D, HelperFan (fan.trans owner) x D →
      (∀ i j, D.R ((borrowedHeaders T i j).castAdd L) = words i j) →
      (∀ j : Fin L, D.L (j.natAdd (T+273)) = [] ∧ D.R (j.natAdd (T+273)) = []) →
      (∀ i, (∀ h, fan h ≠ i) → D.L (owner i) = initial.L i ∧ D.R (owner i) = initial.R i) →
      ∃ z G m out, Exec host code (mk v D) m (mk z G) ∧ (m : ℝ) ≤ price ∧ z.user = v.user ∧
        HelperFan (fan.trans owner) out G ∧ effect out) →
    ∀ v F, (∀ i j, F.R (stage ((borrowedHeaders T i j).castAdd L)) = words i j) →
      (∀ i, F.L (stage (owner i)) = S.L (stage (owner i)) ∧ F.R (stage (owner i)) = S.R (stage (owner i))) →
      (∀ j : Fin L, let k := stage (j.natAdd (T+273)); F.L k = S.L k ∧ F.R k = S.R k) →
      ∃ z G m, Exec (fun f => embProg stage id (host f)) (embProg stage id code) (mk v F) m (mk z G) ∧
        (m : ℝ) ≤ price ∧ z.user = v.user ∧ ∃ out, HelperFan full out G ∧ effect out := by
  intro stage owner full S live free fresh run v F headers keep leaf
  apply liftFanExecution stage (fan.trans owner) host code v F price effect
  exact run (embDn stage v) (embStk stage F) (helperFan_of_agree live (F := F) (fun i => keep (fan i))) headers
    (fun j => ⟨(leaf j).1.trans (free j).1,(leaf j).2.trans (free j).2⟩)
    (fun i h => ⟨(keep i).1.trans (fresh i h).1,(keep i).2.trans (fresh i h).2⟩)

/-- Archive input, leaf scratch and private worker tapes can all be read
from one prepared host outside the live owner and counter tapes. -/
private theorem parentPackedStage_frame {T L w : ℕ} (fan : Fin (142081+2) ↪ Fin T)
    (node : RecursiveInterchangeLayout.Descriptor) (seed S : Stacks (80+((T+273)+L)) prime) :
    let stage := Fin.natAddEmb 80 (m := (T+273)+L)
    let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb L)
    let full := (fan.trans owner).trans stage
    let archive := archiveSetupPlacement 80 T L
    ParentArchiveInput node w (embStk archive seed) →
    (∀ j : Fin L, seed.L (stage (j.natAdd (T+273))) = [] ∧ seed.R (stage (j.natAdd (T+273))) = []) →
    (∀ j, (∀ i, full i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
    ParentArchiveInput node w (embStk archive S) ∧
      (∀ j : Fin L, S.L (stage (j.natAdd (T+273))) = [] ∧ S.R (stage (j.natAdd (T+273))) = []) ∧
      ∀ j, (∀ i, fan i ≠ j) → S.L (stage (owner j)) = seed.L (stage (owner j)) ∧
        S.R (stage (owner j)) = seed.R (stage (owner j)) := by
  intro stage owner full archive prepared blank fresh
  have same j := fresh (archive j) (fun i => Ne.symm ((archiveSetupPlacement_frame j).1 (fan i)))
  have left : (embStk archive S).L = (embStk archive seed).L := funext fun j => (same j).1
  have right : (embStk archive S).R = (embStk archive seed).R := funext fun j => (same j).2
  refine ⟨?_,?_,fun j off => fresh _ (fun i => stage.injective.ne (owner.injective.ne (off i)))⟩
  · unfold ParentArchiveInput at prepared ⊢
    unfold embStk at prepared ⊢
    dsimp only at prepared ⊢
    change S.L ∘ archive = seed.L ∘ archive at left
    change S.R ∘ archive = seed.R ∘ archive at right
    simpa only [left,right] using prepared
  · intro j
    have eq := fresh (stage (j.natAdd (T+273))) (fun i => stage.injective.ne (by
      intro h
      have bad := congrArg Fin.val h
      change (fan i).val = T+273+j.val at bad
      have := (fan i).isLt
      omega))
    exact ⟨eq.1.trans (blank j).1,eq.2.trans (blank j).2⟩

/-- Execute the packed stage after constructing its entire archive from
the parent. Private invocation records are the only worker seed required. -/
theorem parentPackedStage_exec [M8.Machine.Net] {Q w B rows : ℕ} {P U : Type}
    (node : RecursiveInterchangeLayout.Descriptor) (n : Fin 9)
    (tapes : StageRun → ℕ) (body : ∀ p, P → Pr P (tapes p) Q prime U)
    (coeff : StageRun → ℝ) (required : (ℕ → ℕ) → Prop)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (width : node.width = 64*(w+1)) (split : node.rows = 142080*rows)
    (label : node.beforeH = B*prime^(64*((w+1)*64))) :
    let role := {node with rows := rows}
    let K := node.beforeRows*rows*node.between*node.afterD
    let M := prime^(w+1)
    let V := M^16*((M^112*B)*prime^(64*((w+1)*64))*K)
    role.Positive → PackedStageExecution (w := w+1) (B := B) (K := K) n tapes body coeff required →
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ p, Fin (tapes p) ↪ Fin T),
    let stage := Fin.natAddEmb 80 (m := (T+273)+LeafCore.small)
    let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)
    let full := (fan.trans owner).trans stage
    let worker := fun f : (_ : StageRun) × P => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    let host := fun f => embProg stage id (embProg owner id (worker f))
    ∀ childTime, required childTime →
    ∃ seed : Stacks (80+((T+273)+LeafCore.small)) prime, ∃ code, ∀ x u S,
      HelperFan full x S →
      (∀ j, (∀ i, full i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t out, Exec host code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ (((RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152)*V : ℕ)+
          ((stagePackingRate n+(stageRuns.map coeff).sum)*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum) ∧
        z.user = u.user ∧ HelperFan full out F ∧ RestoredBorrowedStage n (w+1) B K x out := by
  intro role K M V pos packed
  obtain ⟨T,fan,bank,build⟩ := packed
  refine ⟨T,fan,bank,?_⟩
  intro stage owner full worker host time ready
  obtain ⟨initial,_,code,run⟩ := build time ready ⟨[],[],fun _ => [],fun _ => []⟩
  obtain ⟨seed,archive,blank,stored⟩ := parentArchiveHost_exists (L := LeafCore.small) node w initial
  obtain ⟨setup,prepare⟩ := parentArchiveThen_exec host capacity
  refine ⟨seed,.seq setup (embProg stage id code),?_⟩
  intro x u S live agrees
  obtain ⟨input,free,privateTapes⟩ := parentPackedStage_frame fan node seed S archive blank agrees
  have fresh i off := And.intro ((privateTapes i off).1.trans (stored i).1)
    ((privateTapes i off).2.trans (stored i).2)
  let price := (stagePackingRate n+(stageRuns.map coeff).sum)*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+
    (((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum : ℕ)
  let post :=  fun F => ∃ out, HelperFan full out F ∧ RestoredBorrowedStage n (w+1) B K x out
  suffices combined : ∃ z G t, Exec host (.seq setup (embProg stage id code)) (mk u S) t (mk z G) ∧
      (t : ℝ) ≤ (((RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152)*V : ℕ)+price ∧
      z.user = u.user ∧ post G by
    obtain ⟨z,G,t,exec,paid,user,out,done,act⟩ := combined
    exact ⟨z,G,t,out,exec,paid,user,done,act⟩
  apply prepare node w B rows width split label pos u S input (embProg stage id code) price post
  exact stageAfterSetup fan (fun f => embProg owner id (worker f)) code _ initial price
    (RestoredBorrowedStage n (w+1) B K x) x S live free fresh (run x)

private theorem archiveFan_view {k T R V : ℕ} (fan : Fin (k+2) ↪ Fin T) (stage : Fin T ↪ Fin R)
    (x : Fin k → Fin V → ZMod 2) (S : Stacks R prime) :
    HelperFan (fan.trans stage) x S ↔ HelperFan fan x (embStk stage S) := Iff.rfl

private theorem chargedStageAfterSetup {T L Q V : ℕ} {P U : Type}
    (fan : Fin (142081+2) ↪ Fin T) (host : P → Pr P ((T+273)+L) Q prime U)
    (code : Pr P ((T+273)+L) Q prime U) (words : Fin 127 → Fin 6 → List (Fin (prime+4)))
    (initial : Stacks T prime) (price : ℕ) (effect : (Fin 142081 → Fin V → ZMod 2) → Prop)
    (x : Fin 142081 → Fin V → ZMod 2) :
    let stage := Fin.natAddEmb 80 (m := (T+273)+L)
    let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb L)
    let full := (fan.trans owner).trans stage
    ∀ S, HelperFan full x S →
    (∀ j : Fin L, S.L (stage (j.natAdd (T+273))) = [] ∧ S.R (stage (j.natAdd (T+273))) = []) →
    (∀ i, (∀ h, fan h ≠ i) → S.L (stage (owner i)) = initial.L i ∧ S.R (stage (owner i)) = initial.R i) →
    (∀ v D, HelperFan (fan.trans owner) x D →
      (∀ i j, D.R ((borrowedHeaders T i j).castAdd L) = words i j) →
      (∀ j : Fin L, D.L (j.natAdd (T+273)) = [] ∧ D.R (j.natAdd (T+273)) = []) →
      (∀ i, (∀ h, fan h ≠ i) → D.L (owner i) = initial.L i ∧ D.R (owner i) = initial.R i) →
      ∃ z G m out, Exec host code (mk v D) m (mk z G) ∧ (∀ js : List _, js.Nodup → m+tapeCharge (fun l r => 4*l.length+2*r.length+4) js G ≤ tapeCharge (fun l r => 4*l.length+2*r.length+4) js D+price) ∧ z.user = v.user ∧
        HelperFan (fan.trans owner) out G ∧ effect out) →
    ∀ v F, (∀ i j, F.R (stage ((borrowedHeaders T i j).castAdd L)) = words i j) →
      (∀ i, F.L (stage (owner i)) = S.L (stage (owner i)) ∧ F.R (stage (owner i)) = S.R (stage (owner i))) →
      (∀ j : Fin L, let k := stage (j.natAdd (T+273)); F.L k = S.L k ∧ F.R k = S.R k) →
      ∃ z G m, Exec (fun f => embProg stage id (host f)) (embProg stage id code) (mk v F) m (mk z G) ∧
        (∀ js : List _, js.Nodup → (m : ℝ)+tapeCharge (fun l r => 4*l.length+2*r.length+4) js G ≤ tapeCharge (fun l r => 4*l.length+2*r.length+4) js F+price) ∧ z.user = v.user ∧ ∃ out, HelperFan full out G ∧ effect out := by
  intro stage owner full S live free fresh run v F headers keep leaf
  have mid := (archiveFan_view (fan.trans owner) stage x F).mp
    (helperFan_of_agree (fan := full) live (F := F) (fun i => keep (fan i)))
  obtain ⟨y,D,m,out,exec,paid,same,done,act⟩ := run (embDn stage v) (embStk stage F) mid headers
    (fun j => ⟨(leaf j).1.trans (free j).1,(leaf j).2.trans (free j).2⟩)
    (fun i off => ⟨(keep i).1.trans (fresh i off).1,(keep i).2.trans (fresh i off).2⟩)
  obtain ⟨z,G,placed,_,user,view,untouched⟩ := exec_emb (ι := id) (body' := fun f => embProg stage id (host f))
    stage.injective (fun _ => rfl) exec v rfl F rfl
  rw [← view] at paid done
  refine ⟨z,G,m,placed,?_,user.trans same,out,(archiveFan_view (fan.trans owner) stage out G).mpr done,act⟩
  intro js unique
  exact_mod_cast placedCleanup_cost_le stage F G _ m price untouched paid js unique

private theorem roundedStageBill {t f s work children : ℕ} {localPrice : ℝ}
    (bill : (t : ℝ)+f ≤ s+localPrice+work+children) :
    t+f ≤ s+(⌈localPrice⌉₊+work+children) := by
  exact_mod_cast (by linarith only [bill,Nat.le_ceil localPrice] :
    (t : ℝ)+f ≤ s+((⌈localPrice⌉₊ : ℝ)+work+children))

/-- Build the archive from parent headers and run the fixed sweep on all independent rows. -/
theorem parentArchiveSweepWithCharge [M8.Machine.Net] (n : Fin 9) :
    let J := Fin 32 × Fin 5
    ∀ (tapes : J → ℕ) (ports : ∀ p, Fin (142081+2) ↪ Fin (tapes p)),
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (banks : ∀ p, Fin (tapes p) ↪ Fin T),
    ∀ {P : J → Type} {U : Type} {Q : ℕ}, columnCapacity ≤ Q →
    (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q →
    ∀ (body : ∀ p, P p → Pr (P p) (tapes p) Q prime U),
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := (Fin.castAddEmb 273 (n := T)).trans scratch
    let host := fun f : (p : J) × P p => embProg (banks f.1) (Sigma.mk f.1) (body f.1 f.2)
    let outer := fun f => embProg owner id (host f)
    let stage := Fin.natAddEmb 80 (m := (T+273)+LeafCore.small)
    let full := (fan.trans owner).trans stage
    let table := fun f => embProg stage id (outer f)
    ∃ setupRate : ℕ, ∃ rate : ℝ, ∀ (call : ∀ p, Pr (P p) (tapes p) Q prime U), ∃ code,
    ∀ (node : RecursiveInterchangeLayout.Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let role := {node with rows := rows}
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := (prime^(w+1))^112*B
    let V := (prime^(w+1))^16*(blocks*prime^(64*((w+1)*64))*K)
    let scale := (V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
    role.Positive → ∀ (work : J → ℕ) (childTime : ℕ → ℕ),
    (∀ p (shared : Stacks (142081+2) prime), ∃ seed : Stacks (tapes p) prime, embStk (ports p) seed = shared ∧
      ∀ a v D, HelperFan (ports p) a D →
        (∀ j, (∀ h, ports p h ≠ j) → D.L j = seed.L j ∧ D.R j = seed.R j) →
        ∃ z F m b, Exec (body p) (call p) (mk v D) m (mk z F) ∧
          (∀ js : List (Fin (tapes p)), js.Nodup →
            m+tapeCharge (fun l r => 4*l.length+2*r.length+4) js F ≤
              tapeCharge (fun l r => 4*l.length+2*r.length+4) js D+(work p+
              ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map childTime).sum)) ∧
          z.user = v.user ∧ HelperFan (ports p) b F ∧ BorrowedStep n (w+1) blocks K p a b) →
    ∃ seed : Stacks (80+((T+273)+LeafCore.small)) prime, ∀ x u S, HelperFan full x S →
      (∀ j, (∀ i, full i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t out, Exec table code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → (t : ℝ)+tapeCharge (fun l r => 4*l.length+2*r.length+4) js F ≤
          tapeCharge (fun l r => 4*l.length+2*r.length+4) js S+(setupRate*V : ℕ)+
          (⌈rate*scale⌉₊+(stageRuns.map work).sum+
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum : ℕ)) ∧
        z.user = u.user ∧ HelperFan full out F ∧ RestoredBorrowedStage n (w+1) B K x out := by
  intro J tapes ports
  obtain ⟨T,fan,banks,build⟩ := allocatedArchiveSweepWithCharge n tapes ports
  refine ⟨T,fan,banks,?_⟩
  intro P U Q capacity headers body scratch owner host outer stage full table
  obtain ⟨rate,compile⟩ := build capacity body
  obtain ⟨setupRate,archive⟩ := parentArchiveThenWithCharge (U := U) headers
  obtain ⟨setup,prepare⟩ := archive table
  refine ⟨setupRate,rate,?_⟩
  intro call
  obtain ⟨sweep,run⟩ := compile call
  refine ⟨.seq setup (embProg stage id sweep),?_⟩
  intro node w B rows width split label role K blocks V scale pos work time supplied
  have hb : 0 < B := Nat.pos_of_mul_pos_right (label ▸ pos.2.2.1)
  have hk : 0 < K := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1) pos.2.2.2.1) pos.2.2.2.2
  have hp := Shared50ModularControl.prime_prime.pos
  have hv : 0 < V := by dsimp only [V,blocks]; positivity
  obtain ⟨initial,_,execute⟩ := run (w+1) B K hv work time supplied ⟨[],[],fun _ => [],fun _ => []⟩
  obtain ⟨seed,input,blank,stored⟩ := parentArchiveHost_exists (L := LeafCore.small) node w initial
  refine ⟨seed,?_⟩
  intro x u S live agrees
  obtain ⟨archiveInput,free,privateTapes⟩ := parentPackedStage_frame fan node seed S input blank agrees
  let price := ⌈rate*scale⌉₊+(stageRuns.map work).sum+
    ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let post := fun G => ∃ out, HelperFan full out G ∧ RestoredBorrowedStage n (w+1) B K x out
  apply Exists.elim (prepare node w B rows width split label pos u S archiveInput
    (embProg stage id sweep) price post ?_)
  · rintro z ⟨F,t,exec,paid,user,out,ready,act⟩
    exact ⟨z,F,t,out,exec,paid,user,ready,act⟩
  apply chargedStageAfterSetup fan outer sweep _ initial price (RestoredBorrowedStage n (w+1) B K x)
    x S live free (fun i off => ⟨(privateTapes i off).1.trans (stored i).1,(privateTapes i off).2.trans (stored i).2⟩)
  intro v F represented ready empty fresh
  obtain ⟨y,D,m,out,exec,paid,same,done,act⟩ := execute x v F represented ready empty fresh
  refine ⟨y,D,m,out,exec,?_,same,done,act⟩
  intro js unique
  have bill := paid js unique
  rw [max_eq_right (Nat.succ_pos w)] at bill
  exact roundedStageBill (localPrice := rate*scale) bill

/-- Place an invocation family on the sweep bank. The restoration worker
uses just the shared owner tapes and has no child procedures. -/
theorem packInvocationFamily [M8.Machine.Net] {Q w B K : ℕ} {P U : Type} (n : Fin 9)
    (tapes : StageRun → ℕ) (ports : ∀ p, Fin (142081+2) ↪ Fin (tapes p))
    (body : ∀ p, P → Pr P (tapes p) Q prime U) (capacity : columnCapacity ≤ Q) :
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    0 < w → 0 < V → ∀ (coeff : StageRun → ℝ) (required : (ℕ → ℕ) → Prop),
    (∀ time, required time → ∀ p, SeededInvocation (w := w) (B := blocks) (K := K) n p (ports p) (body p) (coeff p) time) →
    PackedStageExecution (w := w) (B := B) (K := K) n tapes body coeff required := by
  intro blocks V width pos coeff required supply
  unfold PackedStageExecution
  obtain ⟨T,fan,bank,assemble⟩ := allocatedArchiveSweep_host n tapes ports
  refine ⟨T,fan,bank,?_⟩
  intro scratch owner worker host _ _ time ready shared
  have stage := assemble (P := fun _ => P) capacity body w B K pos coeff time (supply time ready) shared
  simpa only [max_eq_right (show 1 ≤ w from width),add_mul] using stage

open RecursiveInterchangeLayout in
def ScheduledStageRuns [M8.Machine.Net] (n : Fin 9)
    (mt : StageRun → MoveIndex → ℕ) (ct : StageRun → CopyIndex → ℕ)
      (mr : ∀ p i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt p i))
      (cr : ∀ p j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct p j))
      (mT cT : StageRun → ℕ) (mBank : ∀ p i, Fin (mt p i) ↪ Fin (mT p)) (cBank : ∀ p j, Fin (ct p j) ↪ Fin (cT p))
    {P U : Type} {Q : ℕ}
    (mb : ∀ p i, P → Pr P (mt p i) Q prime U) (mf : StageRun → MoveIndex → P)
      (cb : ∀ p j, P → Pr P (ct p j) Q prime U) (cf : StageRun → CopyIndex → P)
    (coeff : StageRun → ℝ) (node : Descriptor) (w B rows : ℕ) : Prop :=
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W →
    let moveChild := fun (p : StageRun) (i : MoveIndex) => phaseChildPositions.choose (n,p,i)
    let copyChild := fun (p : StageRun) (j : CopyIndex) => copyChildPosition (n,p,j)
    let md := fun p i => scheduledChild prime node (moveChild p i)
    let cd := fun p j => scheduledChild prime node (copyChild p j)
    ∀ (record : StageRun → MoveIndex → List (Fin (prime+4))) (copyRecord : StageRun → CopyIndex → List (Fin (prime+4))),
    ∃ (mp : ∀ p i, Fin (volume prime (md p i)) ≃ Fin V) (cp : ∀ p j, Fin (volume prime (cd p j)) ≃ Fin V)
      (banks : ∀ p, InvocationBanks (mT p) (cT p)),
    (∀ p i h, (mp p i h).val = (CopyChildLayout.packActive (md p i) h).val) ∧
    (∀ p j, CopyIntervalPositions (cd p j) (w+1) W (cp p j)) ∧
    PackedStageExecution (w := w+1) (B := B) (K := K) n (fun p => (banks p).tapes)
      (fun p => (banks p).body (mBank p) (cBank p) (mb p) (cb p)) coeff (fun childTime =>
      (∀ p i, ScheduledChildExec node (md p i) w W (mr p i) (record p i) (mp p i) (mb p i) (mf p i) (childTime (moveChild p i).val)) ∧
      (∀ p j, ScheduledChildExec node (cd p j) w W (cr p j) (copyRecord p j) (cp p j) (cb p j) (cf p j) (childTime (copyChild p j).val)))

open RecursiveInterchangeLayout in
/-- A stage uses one state capacity for all of its MOVE and COPY workers.
The local coefficients are selected before the parent dimensions. -/
theorem scheduledInvocationFamily [M8.Machine.Net] (n : Fin 9) :
    let R := Fin 32 × Fin 5
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    ∃ (mt : R → I → ℕ) (ct : R → J → ℕ)
      (mr : ∀ p i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt p i))
      (cr : ∀ p j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct p j))
      (mT cT : R → ℕ) (mBank : ∀ p i, Fin (mt p i) ↪ Fin (mT p)) (cBank : ∀ p j, Fin (ct p j) ↪ Fin (cT p))
      (states : ℕ),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (mb : ∀ p i, P → Pr P (mt p i) Q prime U) (mf : R → I → P)
      (cb : ∀ p j, P → Pr P (ct p j) Q prime U) (cf : R → J → P),
    ∃ coeff : R → ℝ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    ScheduledStageRuns n mt ct mr cr mT cT mBank cBank mb mf cb cf coeff node w B rows := by
  classical
  intro R edges I J
  choose mt ct mr cr mT cT mBank cBank qs banks build using scheduledBorrowedInvocation_host n
  refine ⟨mt,ct,mr,cr,mT,cT,mBank,cBank,max columnCapacity (Finset.univ.sup qs),?_⟩
  intro P U Q cap mb mf cb cf
  choose coeff run using fun p : R => build p ((Finset.le_sup (Finset.mem_univ p)).trans ((le_max_right ..).trans cap)) (mb p) (mf p) (cb p) (cf p)
  refine ⟨coeff,?_⟩
  intro node w B rows width split label
  unfold ScheduledStageRuns
  intro M K blocks W V pos moveChild copyChild md cd record copyRecord
  choose mp cp mcoords ccoords execute using fun p : R =>
    run p node w B rows width split label pos (record p) (copyRecord p)
  refine ⟨mp,cp,banks,mcoords,ccoords,?_⟩
  have live : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
  apply packInvocationFamily (w := w+1) (B := B) (K := K) n (fun p => (banks p).tapes)
    (fun p => (banks p).fan) _ ((le_max_left ..).trans cap) (Nat.succ_pos _) live
  exact fun time ready p => execute p time (ready.1 p) (ready.2 p)

end IntegerMultBounds.MathlibTM2.M6.BitNode
