module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleDispatch

/-! Run the cutoff comparison at each occurrence of the flat remainder schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

theorem mixedIdleSchedule_exec [M8.Machine.Net] {n Q : ℕ} {P U : Type}
    (capacity : columnCapacity ≤ Q) (body : P → Pr P (n+LeafCore.small) Q prime U)
    (node : Descriptor) (i : Fin 9) (w rows L cutoff : ℕ) (aligned : node.width = 64*(w+1))
    (wide : node.width.size ≤ L) (cutFits : cutoff < 2^L)
    (split : node.rows = 142080*rows) (bank : Fin (142081+2) ↪ Fin n)
    (cmp : Fin 10 ↪ Fin (n+LeafCore.small)) (src : Fin 222 → Fin 6 → Fin n)
    (proc : (Fin 32 × Fin 5) × Fin 222 → P) (budget : Fin nodeChildren5.length → ℕ)
    (initial : Stacks (n+LeafCore.small) prime) :
    let fan := bank.trans (Fin.castAddEmb LeafCore.small)
    let W := node.beforeRows*rows*node.beforeH*node.between*node.afterD
    let V := (prime^(w+1))^128*W
    let index := fun k => idleDirectoryIndex (i,idleCopyIndex k)
    let child := fun k => scheduledChild prime node (index k)
    let interval := fun j => let e := idleInterval i j
      phaseIntervalChild e.1 e.2 (w+1) W 64
    let rank := fun j => (idleInterval i j).2-(idleInterval i j).1
    let outside := fun (S : Stacks (n+LeafCore.small) prime) => ∀ t, (∀ l, fan l ≠ t) →
      S.L t = initial.L t ∧ S.R t = initial.R t
    let port := fun k => bank ((idleTape i k).castAdd 2)
    let code := fun k => (ordinaryCutoffTest cmp (rank k.2)).seq (.cond (fun z => symBit (z.scan (cmp 7)))
      (.call (proc k)) (hostedStoppedDirectory capacity (src k.2) (port k)))
    let charge := fun k => (4*w+23*(child k).width+22*L+51 : ℕ) + (if cutoff < (child k).width
      then (budget (index k) : ℝ)+2 else (descriptorHeaderCost (interval k.2) : ℝ) +
        ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
        ((V : ℝ)*((max 1 (child k).width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau))
    0 < V →
    (∀ S, outside S → (S.R (cmp 0)).length = w ∧ S.R (cmp 1) = binSyms L cutoff ∧
      (∀ l : Fin 10, 2 ≤ l.val → S.R (cmp l) = []) ∧
      (∀ j l, S.R ((src j l).castAdd LeafCore.small) = (Routines.hdr (interval j) l).map bitSymbol) ∧
      ∀ l : Fin LeafCore.small, S.L (l.natAdd n) = [] ∧ S.R (l.natAdd n) = []) →
    ∃ position : ∀ k, Fin (volume prime (child k)) ≃ Fin V,
      (∀ k, IdleChildPositions i k.2 (w+1) W (child k) (position k)) ∧
      ((∀ k x u S, cutoff < (child k).width → (child k).width < node.width → HelperFan fan x S → outside S →
        ∃ z F m changed, Exec body (body (proc k)) (mk u S) m (mk z F) ∧ m ≤ budget (index k) ∧
          z.user = u.user ∧ RecordPayload ((port k).castAdd LeafCore.small) (fun _ => blank) 0 changed F ∧
          (∀ t, t ≠ (port k).castAdd LeafCore.small → F.L t = S.L t ∧ F.R t = S.R t) ∧
          ∀ a, changed (position k a) = Shared50RecursiveNodeRows.transpose (one_dvd (child k).rows)
            (x (idleTape i k) ∘ position k) a) →
      ∀ x u S, HelperFan fan x S → outside S →
        ∃ z F m y, Exec body (Prog.seqList (idleCopies.map code)) (mk u S) m (mk z F) ∧
          (m : ℝ) ≤ (idleCopies.map charge).sum+1 ∧ z.user = u.user ∧ HelperFan fan y F ∧
          (∀ k, intervalChildRead i k.2 (w+1) W (x (idleTape i k)) (y (idleTape i k))) ∧
          ∀ t, (∀ k, t ≠ idleTape i k) → y t = x t) := by
  intro fan W V index child interval rank outside port code charge pos metadata
  choose position coords _ using fun k => flatIdleCall_exec body (proc k) node i (idleCopyIndex k)
    (w+1) rows (Nat.succ_pos _) aligned split
  have coord k : IdleChildPositions i k.2 (w+1) W (child k) (position k) := by
    simpa only [idleCopyIndex_get] using coords k
  refine ⟨position,coord,?_⟩
  intro recurse x u S live fresh
  obtain ⟨y,F,z,m,ran,paid,user,ready,read,off⟩ := idleCopies_exec i body code charge (fun _ _ _ => True)
    (fun _ data A => HelperFan fan data A ∧ outside A) (fun k => intervalChildRead i k.2 (w+1) W)
    (by
      intro k past rest data A ctrl _ ready _
      obtain ⟨clock,cut,empty,headers,free⟩ := metadata A ready.2
      have bounds := idleBounds i k.2
      have size : volume prime (interval k.2) = V := intervalChild_volume bounds.1 (bounds.2.trans (by decide)) _ _
      have width : (interval k.2).width = (child k).width := (coord k).1
      have scaled : (w+1)*rank k.2 = (child k).width := (Nat.mul_comm ..).trans width
      have small : (child k).width < node.width := by
        rw [← width,aligned]
        exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.succ_pos w)
      obtain ⟨v,D,m,user,time,run,word,payload,keep,acted⟩ :=
        inheritedDispatch_exec capacity body cmp (src k.2) (port k) _ _ size (position k) width (coord k).2
          (rank k.2) w L cutoff scaled cutFits ((Nat.size_le_size small.le).trans wide) (data (idleTape i k))
          ctrl A clock cut empty pos (headers k.2) (fanPayload ready.1 _) free (proc k) (budget (index k))
          (by
            intro active z
            obtain ⟨v,D,m,word,run,paid,user,out,keep,act⟩ := recurse k data z A active small ready.1 ready.2
            exact ⟨v,D,m,run,paid,user,word,out,keep,act⟩)
      refine ⟨Function.update data (idleTape i k) word,D,v,m,run,time,user,
        ⟨fanUpdate _ word ready.1 payload (fun t ne => keep _ (fan.injective.ne ne)),?_⟩,
        fun _ _ _ => trivial,?_,fun t ne => Function.update_of_ne ne ..⟩
      · intro t away
        have h := keep t (away _).symm
        exact ⟨h.1.trans (ready.2 t away).1,h.2.trans (ready.2 t away).2⟩
      · rw [Function.update_self]
        have eq := ((coord k).2.transpose_iff width _ word).1 acted
        intro a
        simpa only [Fin.cast_cast,Fin.cast_eq_self] using congrFun eq (a.cast size))
    x S u ⟨live,fresh⟩ (fun _ => trivial)
  exact ⟨z,F,m,y,ran,paid,user,ready.1,read,off⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
