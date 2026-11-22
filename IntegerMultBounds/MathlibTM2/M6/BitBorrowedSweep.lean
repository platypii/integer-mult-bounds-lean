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

def PackedBorrowedSweep [M8.Machine.Net] {T Q : ℕ} {U : Type} {P : Option (Fin 32 × Fin 5) → Type}
    (n : Fin 9) (tapes : Option (Fin 32 × Fin 5) → ℕ) (ports : ∀ j, Fin (142081+2) ↪ Fin (tapes j))
    (fan : Fin (142081+2) ↪ Fin T) (body : ∀ j, P j → Pr (P j) (tapes j) Q prime U)
    (host : ((j : Option (Fin 32 × Fin 5)) × P j) → Pr ((j : Option (Fin 32 × Fin 5)) × P j) T Q prime U)
    (C : ℝ) (w B K : ℕ) : Prop :=
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    0 < V → ∀ shared : Stacks (142081+2) prime, ∀ seed : (j : Option (Fin 32 × Fin 5)) → Stacks (tapes j) prime,
    ∃ initial : Stacks T prime, embStk fan initial = shared ∧ ∀ price : Fin 32 × Fin 5 → ℝ,
    (∀ p, ∃ call, ∀ (x : Fin 142081 → Fin V → ZMod 2) u D, HelperFan (ports (some p)) x D →
      (∀ i, (∀ h, ports (some p) h ≠ i) → D.L i = (seed (some p)).L i ∧ D.R i = (seed (some p)).R i) →
      ∃ z F m y, Exec (body (some p)) call (mk u D) m (mk z F) ∧ (m : ℝ) ≤ price p ∧
        z.user = u.user ∧ HelperFan (ports (some p)) y F ∧ BorrowedStep n w blocks K p x y) →
    ∃ code, ∀ x u S, HelperFan fan x S →
      (∀ i, (∀ h, fan h ≠ i) → S.L i = initial.L i ∧ S.R i = initial.R i) →
      ∃ z F t out, Exec host code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ C*((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+(stageRuns.map price).sum ∧
        z.user = u.user ∧ HelperFan fan out F ∧
        RestoredBorrowedStage n w B K x out

/-- Pack each invocation in its actual position, then restore the final helper
charts. The common stage overhead is independent of the invocation budgets. -/
theorem packedBorrowedSweep_host [M8.Machine.Net] (n : Fin 9) :
    let J := Option (Fin 32 × Fin 5)
    ∀ (tapes : J → ℕ) (ports : ∀ j, Fin (142081+2) ↪ Fin (tapes j)),
    let size := fun j : J => (tapes j+127*6)+LeafCore.small
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (size j) ↪ Fin T),
    ∀ {P : J → Type} {U : Type} {Q : ℕ}, columnCapacity ≤ Q →
    ∀ body : ∀ j, P j → Pr (P j) (tapes j) Q prime U,
    let worker := fun (j : J) (f : P j) => embProg (Fin.castAddEmb LeafCore.small (n := tapes j+127*6)) id
      (embProg (Fin.castAddEmb (127*6) (n := tapes j)) id (body j f))
    let host := fun f : (j : J) × P j => embProg (bank f.1) (Sigma.mk f.1) (worker f.1 f.2)
    ∃ C : ℝ, ∀ w B K : ℕ,
    PackedBorrowedSweep n tapes ports fan body host C w B K := by
  intro J tapes ports size
  let full (j : J) := ((ports j).trans (Fin.castAddEmb (127*6))).trans (Fin.castAddEmb LeafCore.small)
  obtain ⟨T,fan,bank,layout⟩ := borrowedSweepBanks n size full
  refine ⟨T,fan,bank,?_⟩
  intro P U Q cap body worker host
  choose pack cost packed using fun p => seededBorrowedCall_host n p (ports (some p)) cap (body (some p))
  obtain ⟨restore,restoreCost,restored⟩ := seededBorrowedRestore_host n (ports none) cap (worker none)
  refine ⟨(stageRuns.map cost).sum+restoreCost,?_⟩
  intro w B K
  unfold PackedBorrowedSweep
  intro blocks V pos shared seed
  choose localSeed _ run using fun p => packed p w B K pos (seed (some p))
  obtain ⟨lastSeed,_,finish⟩ := restored w B K pos (seed none)
  let initialAt : (j : J) → Stacks (size j) prime := Option.rec (motive := fun j => Stacks (size j) prime) lastSeed localSeed
  obtain ⟨initial,view,assemble⟩ := layout shared initialAt
  refine ⟨initial,view,?_⟩
  intro price calls
  let volumeTime := (V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  let charge : J → ℝ := Option.rec (restoreCost*volumeTime) (fun p => cost p*volumeTime+price p)
  obtain ⟨code,execute⟩ := assemble (w := w) (B := B) (K := K) worker charge (by
    intro j
    cases j with
    | none => exact ⟨restore,finish⟩
    | some p =>
      obtain ⟨call,invoke⟩ := calls p
      exact ⟨_,run p call (price p) invoke⟩)
  refine ⟨code,?_⟩
  intro x u S live fresh
  obtain ⟨z,F,t,y,out,exec,paid,user,done,trace,last⟩ := execute x u S live fresh
  refine ⟨z,F,t,out,exec,?_,user,done,restoredBorrowedStage_of_trace trace last⟩
  change (t : ℝ) ≤ (stageRuns.map (fun p => cost p*volumeTime+price p)).sum + restoreCost*volumeTime at paid
  rw [List.sum_map_add,List.sum_map_mul_right] at paid
  dsimp only [volumeTime] at paid
  rw [add_mul]
  linarith only [paid]

end IntegerMultBounds.MathlibTM2.M6.BitNode
