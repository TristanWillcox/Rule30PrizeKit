module

public import Ruliology.CellularAutomata.Rule30XorRigidity

/-!
# A finite deadline for nonlinear XOR collisions in Rule 30

Two incompatible paired colors at initial distance `d` force a nonzero adjacent
cross defect by time `d / 2`. Therefore the XOR of the two histories fails the
Rule 30 update by the next step. The bound is uniform in the histories and the
distance, with no finiteness or boundary assumptions in the whole-line result.

This strengthens the qualitative argument in `Rule30XorRigidity` by retaining
its time horizon. It proves no statement about center-column nonperiodicity,
frequency, or computational complexity.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30XorCollision

open Rule30XorRigidity

namespace HalfLine

open Rule30XorRigidity.HalfLine

/-- Adjacent compatibility through a finite horizon forces compatibility at
distance `d` at every time with at least `d / 2` steps left in that horizon. -/
theorem distant_good_bounded (A B : Nat → Nat → Bool)
    (ha : Rule30XorRigidity.HalfLine.Actual A)
    (hb : Rule30XorRigidity.HalfLine.Actual B)
    (T : Nat)
    (adj : ∀ t, t ≤ T → ∀ i,
      Good (A t (i+1)) (B t (i+1)) (A t (i+2)) (B t (i+2))) (d : Nat) :
    ∀ t p, t + d / 2 ≤ T → 1 ≤ p →
      Good (A t p) (B t p) (A t (p+d)) (B t (p+d)) := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro t p ht hp
    by_cases hd0 : d = 0
    · subst d
      exact good_self _ _
    by_cases hd1 : d = 1
    · subst d
      have h := adj t (by omega) (p-1)
      simpa [show p-1+1=p by omega, show p-1+2=p+1 by omega] using h
    apply Classical.byContradiction
    intro bad
    have mid : ∀ k, p < k → k < p+d → A t k=false ∧ B t k=false := by
      intro k hpk hkd
      have l := ih (k-p) (by omega) t p (by omega) hp
      have r := ih (p+d-k) (by omega) t k (by omega) (by omega)
      rw [show p+(k-p)=k by omega] at l
      rw [show k+(p+d-k)=p+d by omega] at r
      exact middle_zero _ _ _ _ _ _ bad l r
    by_cases hd2 : d = 2
    · subst d
      obtain ⟨az,bz⟩ := mid (p+1) (by omega) (by omega)
      have next := ih 1 (by omega) (t+1) p (by omega) hp
      have right := adj t (by omega) (p+1)
      change Good (A t (p+2)) (B t (p+2)) (A t (p+3)) (B t (p+3)) at right
      rw [ha t p, hb t p, ha t (p+1), hb t (p+1), az,bz,
        show p+1+1=p+2 by omega, show p+1+2=p+3 by omega] at next
      exact bad (gap_two _ _ _ _ _ _ right next)
    · obtain ⟨a1,b1⟩ := mid (p+1) (by omega) (by omega)
      obtain ⟨a2,b2⟩ := mid (p+2) (by omega) (by omega)
      obtain ⟨az,bz⟩ := mid (p+d-2) (by omega) (by omega)
      obtain ⟨az1,bz1⟩ := mid (p+d-1) (by omega) (by omega)
      have next := ih (d-2) (by omega) (t+1) p (by omega) hp
      rw [show p+(d-2)=p+d-2 by omega, ha t p, hb t p,
        ha t (p+d-2), hb t (p+d-2),
        show p+d-2+1=p+d-1 by omega, show p+d-2+2=p+d by omega,
        a1,b1,a2,b2,az,bz,az1,bz1] at next
      exact bad (gap_large _ _ _ _ next)

end HalfLine

/-- Finite-horizon compatibility on the whole triangular-coordinate line. -/
theorem distant_good_bounded (A B : Nat → Int → Bool)
    (ha : Actual A) (hb : Actual B) (T d t : Nat) (p : Int)
    (adj : ∀ s, s ≤ T → ∀ i,
      Rule30XorRigidity.HalfLine.Good (A s i) (B s i) (A s (i+1)) (B s (i+1)))
    (ht : t + d / 2 ≤ T) :
    Rule30XorRigidity.HalfLine.Good (A t p) (B t p)
      (A t (p+(d:Int))) (B t (p+(d:Int))) := by
  let k := p-1
  have cadj : ∀ s, s ≤ T → ∀ i,
      Rule30XorRigidity.HalfLine.Good
        (cut A k s (i+1)) (cut B k s (i+1))
        (cut A k s (i+2)) (cut B k s (i+2)) := by
    intro s hs i
    change Rule30XorRigidity.HalfLine.Good
      (A s (k+((i+1:Nat):Int))) (B s (k+((i+1:Nat):Int)))
      (A s (k+((i+2:Nat):Int))) (B s (k+((i+2:Nat):Int)))
    rw [show k+((i+1:Nat):Int)=k+(i:Int)+1 by omega,
      show k+((i+2:Nat):Int)=(k+(i:Int)+1)+1 by omega]
    exact adj s hs (k+(i:Int)+1)
  have h := HalfLine.distant_good_bounded (cut A k) (cut B k)
    (cut_actual A ha k) (cut_actual B hb k) T cadj d t 1 ht (by omega)
  change Rule30XorRigidity.HalfLine.Good
    (A t (k+1)) (B t (k+1))
    (A t (k+((1+d:Nat):Int))) (B t (k+((1+d:Nat):Int))) at h
  simpa only [show k+1=p by dsimp [k]; omega,
    show k+((1+d:Nat):Int)=p+(d:Int) by dsimp [k]; omega] using h

/-- An incompatible pair forces an adjacent defect by half its separation. -/
theorem adjacent_collision_triangular (A B : Nat → Int → Bool)
    (ha : Actual A) (hb : Actual B) (p : Int) (d : Nat)
    (bad : ¬ Rule30XorRigidity.HalfLine.Good (A 0 p) (B 0 p)
      (A 0 (p+(d:Int))) (B 0 (p+(d:Int)))) :
    ∃ t, t ≤ d / 2 ∧ ∃ x,
      ¬ Rule30XorRigidity.HalfLine.Good (A t x) (B t x) (A t (x+1)) (B t (x+1)) := by
  apply Classical.byContradiction
  intro hn
  apply bad
  apply distant_good_bounded A B ha hb (d/2) d 0 p
  · intro t ht x
    apply Classical.byContradiction
    intro hx
    exact hn ⟨t,ht,x,hx⟩
  · omega

/-- Ordinary left/center/right coordinates; no support assumptions. -/
theorem adjacent_collision (A B : Nat → Int → Bool)
    (ha : Standard A) (hb : Standard B) (p : Int) (d : Nat)
    (bad : ¬ Rule30XorRigidity.HalfLine.Good (A 0 p) (B 0 p)
      (A 0 (p+(d:Int))) (B 0 (p+(d:Int)))) :
    ∃ t, t ≤ d / 2 ∧ ∃ x,
      ¬ Rule30XorRigidity.HalfLine.Good (A t x) (B t x) (A t (x+1)) (B t (x+1)) := by
  obtain ⟨t,ht,i,hi⟩ := adjacent_collision_triangular (shear A) (shear B)
    ((shear_actual_iff A).mpr ha) ((shear_actual_iff B).mpr hb) p d
    (by simpa [shear] using bad)
  refine ⟨t,ht,(t:Int)+i,?_⟩
  simpa [shear,Int.add_assoc] using hi

/-- At the collision site, the XOR history violates the ordinary Rule 30
update. The output time `t+1` is at most `d/2+1`. -/
theorem xor_update_fails (A B : Nat → Int → Bool)
    (ha : Standard A) (hb : Standard B) (p : Int) (d : Nat)
    (bad : ¬ Rule30XorRigidity.HalfLine.Good (A 0 p) (B 0 p)
      (A 0 (p+(d:Int))) (B 0 (p+(d:Int)))) :
    ∃ t, t+1 ≤ d/2+1 ∧ ∃ x,
      (A (t+1) x ^^ B (t+1) x) ≠
        Rule30Jen.rule (A t (x-1) ^^ B t (x-1))
          (A t x ^^ B t x) (A t (x+1) ^^ B t (x+1)) := by
  obtain ⟨t,ht,x,hx⟩ := adjacent_collision A B ha hb p d bad
  refine ⟨t,by omega,x,?_⟩
  intro he
  apply hx
  rw [ha t x,hb t x] at he
  exact (Rule30XorRigidity.HalfLine.local_cross _ _ _ _ _ _).mp he.symm

end Ruliology.CellularAutomata.Rule30XorCollision
