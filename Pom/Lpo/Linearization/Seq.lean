import Pom.Lpo.Operations.Seq
import Pom.Linearization

open Linearization

namespace Lpofin

lemma lin_seq {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [PartialOrder act] [Sem act s (t s)]
    [PartialOrder test] [Sem test s (t Bool)]
    (α β : Lpofin (Label act test)) (f : CopyFn α β) :
    (lin (seq α β f) : s → t s) = fun σ ↦ lin α σ >>= lin β := by sorry

end Lpofin
