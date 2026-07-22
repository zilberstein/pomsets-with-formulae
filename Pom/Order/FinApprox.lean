import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Basic
import Mathlib.Order.Atoms
import Mathlib.Order.KonigLemma
import DomainTheory.Compactness

import Pom.Order
import Pom.Lpo.Order.FinApprox

def Pomfin (l : Type) [Bot l] : Type := Quotient (@Lpofin.instSetoid l _)

namespace Pomfin

def mk {l : Type} [Bot l] : Lpofin l → Pomfin l := Quotient.mk'

instance {l : Type} [Bot l] : Membership (Lpofin l) (Pomfin l) where
  mem p α := p = Pomfin.mk α

def to_pom {l : Type} [Bot l] (p : Pomfin l) : Pom l :=
  p.map Subtype.val (fun _ _ heq ↦ heq)

lemma to_pom_injective {l : Type} [Bot l] : Function.Injective (@to_pom l _) := by
  intro p q heq
  obtain ⟨α, rfl⟩ := p.exists_rep
  obtain ⟨β, rfl⟩ := q.exists_rep
  have : Pom.mk (α.val) = Pom.mk (β.val) := by
    refine (Quotient.map_mk Subtype.val _ _).symm.trans (heq.trans ?_)
    exact Quotient.map_mk _ _ _
  have heq := Quotient.eq_iff_equiv.mp this
  refine Quotient.eq_iff_equiv.mpr heq

instance {l : Type} [Bot l] : Coe (Pomfin l) (Pom l) where
  coe := Pomfin.to_pom

instance {l : Type} [LE l] [Bot l] : LE (Pomfin l) where
  le p q := p.to_pom ≤ q.to_pom

instance {l : Type} [PartialOrder l] [OrderBot l] : PartialOrder (Pomfin l) where
  le_refl _ := @le_refl (Pom l) _ _
  le_trans _ _ _ := @le_trans (Pom l) _ _ _ _
  le_antisymm _ _ hpq hqp :=
    to_pom_injective (@le_antisymm (Pom l) _ _ _ hpq hqp)

lemma to_pom_mono {l : Type} [PartialOrder l] [OrderBot l] :
    Monotone (@Pomfin.to_pom l _) := fun _ _ hle ↦ hle

lemma pom_mk {l : Type} [Bot l] {α : Lpofin l} : Pomfin.mk α = Pom.mk α.val := rfl

lemma val_mem_to_pom {l : Type} [Bot l] {α : Lpofin l} {p : Pomfin l} :
    α ∈ p ↔ α.val ∈ p.to_pom := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; refine to_pom_injective ?_
    exact h.trans pom_mk;

lemma le_iff {l : Type} [LE l] [OrderBot l] {p q : Pomfin l} :
    p ≤ q ↔ ∃ α ∈ p, ∃ β ∈ q, α ≤ β := by
  constructor
  · intro hle
    obtain ⟨β, rfl⟩ := q.exists_rep
    obtain ⟨α, hα, hle'⟩ := Pom.ge_lpo hle
    refine ⟨⟨α, ?_⟩, ?_, β, rfl, hle'⟩
    · exact β.property.subset hle'.nodes
    · exact val_mem_to_pom.mpr hα
  · rintro ⟨α, rfl, β, rfl, hle⟩
    refine ⟨α.val, ?_, β.val, ?_, hle⟩ <;> exact val_mem_to_pom.mp rfl

lemma lift_monotone {l X : Type} [PartialOrder l] [OrderBot l] [Preorder X]
    {f : Lpofin l → X} {h : ∀ α β, α ≈ β → f α = f β}
    (hmono : Monotone f) : Monotone (fun p : Pomfin l ↦ p.lift f h) := by
  intro _ _ hle
  obtain ⟨a, rfl, b, rfl, hle'⟩ := Pomfin.le_iff.mp hle
  refine le_of_eq_of_le (Quotient.lift_mk _ _ _) ?_
  refine le_of_le_of_eq ?_ (Quotient.lift_mk _ _ _).symm
  exact hmono hle'

end Pomfin
