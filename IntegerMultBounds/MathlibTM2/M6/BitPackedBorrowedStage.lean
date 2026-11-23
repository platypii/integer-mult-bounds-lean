module

public import IntegerMultBounds.MathlibTM2.M6.BitChargedChartWorker

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 RecursiveInterchangeLayout

private theorem archiveBill {t f s setup p : ℕ} (paid : (t : ℝ)+f ≤ s+setup+p) :
    t+f ≤ s+(setup+p) := by
  exact_mod_cast (by simpa only [add_assoc] using paid : (t : ℝ)+f ≤ s+(setup+(p : ℝ)))

/-- Run the parent archive and corrected borrowed sweep as a single flat node piece. -/
theorem packedBorrowedStageWithCharge [M8.Machine.Net] (n : Fin 9) :
    let J := Fin 32 × Fin 5
    ∀ (tapes : J → ℕ) (ports : ∀ p, Fin (142081+2) ↪ Fin (tapes p)),
    ∃ states : ℕ, ∀ {P : J → Type} {U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (body : ∀ p, P p → Pr (P p) (tapes p) Q prime U) (call : ∀ p, Pr (P p) (tapes p) Q prime U),
    ∃ (T : ℕ) (host : ((p : J) × P p) → Pr ((p : J) × P p) T Q prime U) (program : Pr ((p : J) × P p) T Q prime U)
      (src dst : Fin (142081+2) ↪ Fin T), ∃ (setup base chartTapes : ℕ) (sweepRate chartRate : ℝ),
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
    let W := B*prime^(64*((w+1)*64))*K
    let size : (prime^(w+1))^128*W = V := (ordinaryCompact_width _ W).symm.trans (by simp [V,W,blocks,Nat.mul_assoc])
    let localWork := setup*V+⌈sweepRate*scale⌉₊+(stageRuns.map work).sum+
      13*((base*V+17760*(2*LeafCore.coreCost V (w+1)+14))*(chartTapes+5)+12)+
      ⌈chartRate*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(10*V+10)+1)
    let children := ((List.range' (stageChildStart n)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum
    ∃ seed, PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin W,
      let address := fun z => (flatWindowEquiv (w+1) W (windowState (w+1) z,j)).cast size
      readRoles address y = (Piece.stage n).run (readRoles address x))
      host program src dst seed (localWork+children) := by
  intro J tapes ports
  obtain ⟨chartRate,base,chartTapes,chartStates,chart⟩ := borrowedFlatHandoffWithCharge
  obtain ⟨T,fan,banks,compile⟩ := parentArchiveSweepWithCharge n tapes ports
  let headerStates := (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)
  refine ⟨max chartStates (max columnCapacity headerStates),?_⟩
  intro P U Q fits body call
  have room := (le_max_right _ _).trans fits
  obtain ⟨setup,sweepRate,build⟩ := compile ((le_max_left _ _).trans room) ((le_max_right _ _).trans room) body
  obtain ⟨worker,execute⟩ := build call
  let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)
  let stage := Fin.natAddEmb 80 (m := T+273+LeafCore.small)
  let table := fun f : (p : J) × P p => embProg stage id (embProg owner id
    (embProg (banks f.1) (Sigma.mk f.1) (body f.1 f.2)))
  obtain ⟨R,host,program,src,dst,handoff⟩ := chart n ((fan.trans owner).trans stage) table worker ((le_max_left _ _).trans fits)
  refine ⟨R,host,program,src,dst,setup,base,chartTapes,sweepRate,chartRate,?_⟩
  intro node w B rows width split label role K blocks V scale positive work childTime supplied W size localWork children
  obtain ⟨initial,run⟩ := execute node w B rows width split label positive work childTime supplied
  have hb : 0 < B := Nat.pos_of_mul_pos_right (label ▸ positive.2.2.1)
  have hk : 0 < K := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.2.1) positive.2.2.2.2
  let price := setup*V+(⌈sweepRate*scale⌉₊+(stageRuns.map work).sum+children)
  obtain ⟨seed,built⟩ := handoff (w := w+1) (B := B) (K := K) price initial (Nat.succ_pos _) hb hk (by
    intro x u S live frame
    obtain ⟨z,F,t,y,exec,paid,user,out,act⟩ := run x u S live frame
    refine ⟨z,F,t,y,exec,?_,user,out,act⟩
    intro js unique
    exact archiveBill (paid js unique))
  refine ⟨seed,?_⟩
  have costs (setup sweep work corrections charts output children : ℕ) :
      corrections+(setup+(sweep+work+children))+charts+output =
      (setup+sweep+work+corrections+charts+output)+children := by omega
  change PackedPieceHandoffWithCharge _ _ _ _ _ _ _ _ (_+price+_+_) at built
  dsimp only [price] at built
  rw [costs] at built
  exact built

end IntegerMultBounds.MathlibTM2.M6.BitNode
