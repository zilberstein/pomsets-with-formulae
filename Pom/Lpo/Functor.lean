import Pom.Lpo.Basic
import Pom.Lpo.FinApprox

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

end Lpo

namespace Lpofin

def map {l l' : Type} [Bot l] [Bot l'] (f : l → l') (α : Lpofin l)
    (hbot : ∀ x, x = ⊥ ↔ f x = ⊥) : Lpofin l' := {
  val := α.val.map f hbot
  property := α.property
}

end Lpofin
