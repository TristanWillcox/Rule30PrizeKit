module

public import Ruliology.CellularAutomata.Rule30XorRigidity
public import Ruliology.CellularAutomata.Rule30XorCollision

/-!
# Sharpness witnesses for the quantitative XOR collision bound

Two single-cell seeds at distance d have no nonlinear cross defect before d/2.
This file is developed against the pinned official kit, using ordinary kernel proofs.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30XorSharpness

open Rule30Jen
open Rule30XorRigidity (Standard)
open Rule30XorRigidity.HalfLine (Good local_cross)

def evolve (s : Int → Bool) : Nat → Int → Bool
  | 0, x => s x
  | t+1, x => rule (evolve s t (x-1)) (evolve s t x) (evolve s t (x+1))

theorem evolve_standard (s : Int → Bool) : Standard (evolve s) := by
  intro t x
  rfl

/-- The deadline also bounds disagreement with the actual evolution of the XOR initial row. -/
theorem superposition_disagrees_by (A B : Nat → Int → Bool)
    (ha : Standard A) (hb : Standard B) (p : Int) (d : Nat)
    (bad : ¬ Good (A 0 p) (B 0 p) (A 0 (p+(d:Int))) (B 0 (p+(d:Int)))) :
    ∃ s, s ≤ d/2+1 ∧ ∃ x,
      evolve (fun y => A 0 y ^^ B 0 y) s x ≠ (A s x ^^ B s x) := by
  apply Classical.byContradiction
  intro hn
  have agree : ∀ s, s ≤ d/2+1 → ∀ x,
      evolve (fun y => A 0 y ^^ B 0 y) s x = (A s x ^^ B s x) := by
    intro s hs x
    apply Classical.byContradiction
    intro hx
    exact hn ⟨s,hs,x,hx⟩
  obtain ⟨t,ht,x,hx⟩ := Rule30XorCollision.xor_update_fails A B ha hb p d bad
  apply hx
  rw [← agree (t+1) ht x]
  change rule (evolve (fun y => A 0 y ^^ B 0 y) t (x-1))
      (evolve (fun y => A 0 y ^^ B 0 y) t x)
      (evolve (fun y => A 0 y ^^ B 0 y) t (x+1)) = _
  rw [agree t (by omega) (x-1), agree t (by omega) x, agree t (by omega) (x+1)]

def single (p : Int) : Nat → Int → Bool := evolve (fun x => decide (x=p))

theorem single_support (p : Int) : ∀ t x, single p t x = true →
    p - (t : Int) ≤ x ∧ x ≤ p + (t : Int) := by
  intro t
  induction t with
  | zero =>
      intro x hx
      simp [single, evolve] at hx
      omega
  | succ t ih =>
      intro x hx
      apply Classical.byContradiction
      intro outside
      have h1 : single p t (x-1) = false := by
        cases h : single p t (x-1) with
        | false => rfl
        | true => have := ih (x-1) h; omega
      have h2 : single p t x = false := by
        cases h : single p t x with
        | false => rfl
        | true => have := ih x h; omega
      have h3 : single p t (x+1) = false := by
        cases h : single p t (x+1) with
        | false => rfl
        | true => have := ih (x+1) h; omega
      change rule (single p t (x-1)) (single p t x) (single p t (x+1)) = true at hx
      rw [h1,h2,h3] at hx
      contradiction

theorem before_collision (d t : Nat) (ht : t < d/2) (x : Int) :
    Good (single 0 t x) (single d t x) (single 0 t (x+1)) (single d t (x+1)) := by
  have left : (single 0 t x && single d t (x+1)) = false := by
    cases ha : single 0 t x <;> cases hb : single d t (x+1) <;> try rfl
    have := single_support 0 t x ha
    have := single_support d t (x+1) hb
    omega
  have right : (single 0 t (x+1) && single d t x) = false := by
    cases ha : single 0 t (x+1) <;> cases hb : single d t x <;> try rfl
    have := single_support 0 t (x+1) ha
    have := single_support d t x hb
    omega
  exact left.trans right.symm

def combined (d : Nat) : Nat → Int → Bool :=
  evolve (fun x => single 0 0 x ^^ single d 0 x)

theorem superposition_through (d : Nat) : ∀ t, t ≤ d/2 → ∀ x,
    combined d t x = (single 0 t x ^^ single d t x) := by
  intro t
  induction t with
  | zero => intro ht x; rfl
  | succ t ih =>
      intro ht x
      have prev := ih (by omega)
      change rule (combined d t (x-1)) (combined d t x) (combined d t (x+1)) = _
      rw [prev (x-1), prev x, prev (x+1)]
      exact (local_cross _ _ _ _ _ _).mpr (before_collision d t (by omega) x)

theorem initial_incompatible (d : Nat) (hd : 0 < d) :
    ¬ Good (single 0 0 0) (single d 0 0) (single 0 0 (0+(d:Int)))
      (single d 0 (0+(d:Int))) := by
  simp [Good, single, evolve, show (0:Int) ≠ d by omega]

/-- For every positive separation, a determinant defect occurs exactly at d/2. -/
theorem collision_at_half (d : Nat) (hd : 0 < d) :
    ∃ x, ¬ Good (single 0 (d/2) x) (single d (d/2) x)
      (single 0 (d/2) (x+1)) (single d (d/2) (x+1)) := by
  obtain ⟨t,ht,x,hx⟩ := Rule30XorCollision.adjacent_collision
    (single 0) (single d) (evolve_standard _) (evolve_standard _) 0 d
    (initial_incompatible d hd)
  have eq : t = d/2 := by
    by_cases hlt : t < d/2
    · exact False.elim (hx (before_collision d t hlt x))
    · omega
  subst t
  exact ⟨x,hx⟩

/-- The sharp bound concerns actual evolution from the XOR initial row:
agreement holds at every site through time d/2, and fails somewhere at d/2+1. -/
theorem first_disagreement (d : Nat) (hd : 0 < d) :
    (∀ t, t ≤ d/2 → ∀ x, combined d t x = (single 0 t x ^^ single d t x)) ∧
    (∃ x, combined d (d/2+1) x ≠ (single 0 (d/2+1) x ^^ single d (d/2+1) x)) := by
  refine ⟨superposition_through d, ?_⟩
  obtain ⟨x,hx⟩ := collision_at_half d hd
  refine ⟨x, ?_⟩
  intro he
  apply hx
  change rule (combined d (d/2) (x-1)) (combined d (d/2) x)
      (combined d (d/2) (x+1)) = _ at he
  rw [superposition_through d (d/2) (by omega) (x-1),
      superposition_through d (d/2) (by omega) x,
      superposition_through d (d/2) (by omega) (x+1)] at he
  exact (local_cross _ _ _ _ _ _).mp he

end Ruliology.CellularAutomata.Rule30XorSharpness
