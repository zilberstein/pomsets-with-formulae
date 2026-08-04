import Pom.Lpo.Basic
import Pom.Lpo.Order.FinApprox

namespace Lpo

def map {l l' : Type} [Bot l] [Bot l'] (f : l → l') (α : Lpo l)
    (hbot : ∀ x, x = ⊥ ↔ f x = ⊥) : Lpo l' := {
  val := {
    nodes := α.nodes
    rel := α.rel
    lab x := f (α.lab x)
    form := α.form
  }
  property := by
    constructor
    · exact α.property.rel_dom
    · simp only [Lpo.lab]; intro _ hx
      refine (hbot _).mp ?_
      exact α.property.lab_dom _ hx
    · exact α.property.rel
    · simp only [Lpo.lab]; intro x hx
      exact (α.property.bot x) ((hbot _).mpr hx)
    · exact α.property.form_dom
    · exact α.property.form
}

lemma map_isomorphic {l l' : Type} [Bot l] [Bot l'] {f : l → l'} (α β : Lpo l)
    (hbot : ∀ x, x = ⊥ ↔ f x = ⊥) (h : α ≈ β) :
    α.map f hbot ≈ β.map f hbot := by
  have ⟨e, heq⟩ := h; use e; ext1
  · rfl
  · simp only [rel, map]; exact congrArg Lpo.rel heq
  · simp only [lab, map]; ext x; by_cases hx : x ∈ β.nodes
    · refine (dif_pos hx).trans (congrArg f ?_)
      refine Eq.trans ?_ (congrFun (congrArg Lpo.lab heq) x)
      symm; exact dif_pos hx
    · rw [β.property.lab_dom _ hx |> (hbot _).mp]
      exact dif_neg hx
  · simp only [form, map]; exact congrArg Lpo.form heq

end Lpo

namespace Lpofin

def map {l l' : Type} [Bot l] [Bot l'] (f : l → l') (α : Lpofin l)
    (hbot : ∀ x, x = ⊥ ↔ f x = ⊥) : Lpofin l' := {
  val := α.val.map f hbot
  property := α.property
}

end Lpofin
