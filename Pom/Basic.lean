import Pom.Lpo.Basic
import Pom.Lpo.Order
import Pom.Lpo.Isomorphism
import Pom.Lpo.FinApprox

def Pom (l : Type) [Bot l] : Type := Quotient (@Lpo.instSetoid l _)

namespace Pom

def mk {l : Type} [Bot l] : Lpo l → Pom l := Quotient.mk'

instance {l : Type} [Bot l] : Membership (Lpo l) (Pom l) where
  mem p α := p = Pom.mk α

instance {l : Type} [LE l] [Bot l] : LE (Pom l) where
  le p q := ∃ a ∈ p, ∃ b ∈ q, a ≤ b

def singleton {l : Type} [Bot l] (ℓ : l) : Pom l :=
  Pom.mk (Lpo.singleton default ℓ)

lemma singleton_equiv {l : Type} [Bot l] {x y : Node} (ℓ : l) :
    Lpo.singleton x ℓ ≈ Lpo.singleton y ℓ := by
  use {
    toFun _ := ⟨y, Set.mem_singleton _⟩
    invFun _ := ⟨x, Set.mem_singleton _⟩
    left_inv x := by ext; symm; exact Set.mem_singleton_iff.mp x.property
    right_inv x := by ext; symm; exact Set.mem_singleton_iff.mp x.property
  }
  ext1
  · simp only [Lpo.permute, Lpo.singleton, Lpo.nodes]
  · ext u v; simp only [Lpo.rel, Lpo.permute, Lpo.singleton]; constructor
    · rintro ⟨_, _, f⟩; exact f
    · exact False.elim
  · ext z; simp only [Lpo.lab, Lpo.permute, Lpo.singleton, Lpo.nodes]
    by_cases heq : y = z
    · subst heq; simp only [Set.mem_singleton_iff, ↓reduceDIte, ↓reduceIte]
      refine dif_pos ?_; rfl
    · simp only [Set.mem_singleton_iff, heq, ↓reduceIte, dite_eq_right_iff, ite_eq_right_iff]
      rintro rfl; contradiction
  · simp only [Lpo.form, Lpo.permute, Lpo.nodes, Lpo.singleton, Set.mem_singleton_iff,
      Equiv.symm_mk, Form.permute]
    ext z v; constructor
    · rintro ⟨rfl, _⟩; simp only [↓reduceIte]; trivial
    · intro h; by_cases heq : y = z
      · subst heq; refine ⟨rfl, ?_⟩
        conv => exact congrFun (if_pos rfl) _
        trivial
      · simp only [heq, ↓reduceIte] at h; exfalso; exact h

end Pom
