import Pom.Lpo.Basic
import Pom.Lpo.Order
import Pom.Lpo.Order.FinApprox
import Pom.Lpo.Isomorphism
import Pom.Lpo.Linearization.Label
import Pom.Lpo.Operations.Seq.Isomorphism

namespace Linearization

class Nondet (α : Type) where
  nondet {ι : Type} [Finite ι] : (ι → α) → α

  nondet_congr {ι κ : Type} [Finite ι] [Finite κ]
    {f : ι → α} {g : κ → α} (e : ι ≃ κ) (h : f = g ∘ e) :
    nondet f = nondet g
  nondet_singleton {ι : Type} [Unique ι] {f : ι → α} :
    nondet f = f default

namespace Nondet

lemma convert {α ι : Type} {X Y : Finset ι} [Nondet α]
    {f : ↑X → α} (h : X = Y) :
    Nondet.nondet f = Nondet.nondet fun x : ↑Y ↦ f ⟨x.val, h ▸ x.property⟩:= by
  subst h; rfl

lemma finset_congr {α ι : Type} {X Y : Finset ι} [Nondet α]
    {f : ↑X → α} {g : ↑Y → α}
    (h : X = Y) (h' : f = g ∘ fun x ↦ ⟨x.val, h ▸ x.property⟩) :
    nondet f = nondet g := by
  subst h'; symm; exact convert h.symm

lemma finset_singleton {α ι : Type} {X : Finset ι} [Nondet α] (x : ι)
    {f : ↑X → α} (h : X = {x}) :
    Nondet.nondet f = f ⟨x, h ▸ Finset.mem_singleton_self _⟩ := by
  subst h; exact nondet_singleton

end Nondet

open OmegaCompletePartialOrder

class Sem (c : Type) (in_type out_type : Type) [Preorder c] [Preorder out_type] where
  sem : c → in_type → out_type

  sem_mono : Monotone sem

class ContinuousMonad (t : Type → Type) [Monad t]
    [∀ α, OmegaCompletePartialOrder (t α)] [∀ α, Bot (t α)] where
  bind_mono {α β : Type} :
    ∀ {m₁ m₂ : t α} {k₁ k₂ : α → t β}, m₁ ≤ m₂ → k₁ ≤ k₂ → (m₁ >>= k₁) ≤ (m₂ >>= k₂)
  bind_continuous {α β : Type}  :
    ∀ {c₁ : Chain (t α)} {c₂ : Chain (α → t β)},
      (ωSup c₁ >>= ωSup c₂) = ωSup {
        toFun n := c₁ n >>= c₂ n
        monotone' _ _ hle := bind_mono (c₁.monotone' hle) (c₂.monotone' hle)
      }
  bind_strict {α β : Type} :
    ∀ {f : α → t β}, ⊥ >>= f = ⊥

class Linearizable (t : Type → Type) (α : Type)
  [∀ α, OmegaCompletePartialOrder (t α)] [∀ α, Bot (t α)]
  extends Monad t, ContinuousMonad t, LawfulMonad t, Nondet (t α) where
  nondet_mono {ι : Type} [Finite ι] : Monotone (@nondet ι _)
  nondet_continuous {ι : Type} [Finite ι] : ωScottContinuous (@nondet ι _)

  bind_additive {ι : Type} [Finite ι] (κ : ι → t α) (f : α → t α) :
    nondet κ >>= f = nondet fun i ↦ κ i >>= f

end Linearization

namespace Lpofin

open Linearization

open Classical in
noncomputable def next {l : Type} [Bot l] (a : Lpofin l) (s : Finset Node) (φ : Form Node) :
    Finset Node :=
  a.nodes_finset.filter fun x ↦ x ∈ s ∧ φ ≤ a.form x ∧ ∀ y, a.rel y x → y ∉ s

lemma next_empty {l : Type} [Bot l] {a : Lpofin l} {φ : Form Node} :
    next a ∅ φ = ∅ := by
  ext x; constructor
  · intro h; classical obtain ⟨_, ⟨⟩, _⟩ := Finset.mem_filter.mp h
  · rintro ⟨⟩

open Classical in
noncomputable def filter_by_outcome {l : Type} [Bot l]
    (α : Lpofin l) (s : Finset Node) (x : Node) (b : Bool) : Finset Node :=
  (s.erase x).filter fun z ↦
    Form.sat
      ((α.form z).and
        (bif b then (Form.literal x) else (Form.literal x).not))

open Classical in
lemma filter_by_outcome_inter {l : Type} [LE l] [Bot l]
    {α β : Lpofin l} {s : Finset Node} {x : Node} {b : Bool} (hle : α ≤ β) :
    filter_by_outcome α (s ∩ α.nodes_finset) x b = filter_by_outcome β s x b ∩ α.nodes_finset := by
  ext y; constructor
  · intro hy; have ⟨hy, hform⟩ := Finset.mem_filter.mp hy
    rw [← Finset.erase_inter] at hy
    have ⟨hye, hyα⟩ := Finset.mem_inter.mp hy
    refine Finset.mem_inter.mpr ⟨?_, hyα⟩
    conv at hform => arg 1; arg 1; exact hle.form _ <| α.property.mem_toFinset.mp hyα
    exact Finset.mem_filter.mpr ⟨hye, hform⟩
  · intro hy; have ⟨hy, hyα⟩ := Finset.mem_inter.mp hy
    have ⟨hye, hform⟩ := Finset.mem_filter.mp hy
    conv at hform => arg 1; arg 1; exact (hle.form _ <| α.property.mem_toFinset.mp hyα).symm
    refine Finset.mem_filter.mpr ⟨?_, hform⟩
    rw [← Finset.erase_inter]; exact Finset.mem_inter.mpr ⟨hye, hyα⟩

open Classical in
lemma filter_by_outcome_sub_erase {l : Type} [Bot l]
    {α : Lpofin l} {s : Finset Node} {x : Node} {b : Bool} :
    filter_by_outcome α s x b ⊆ s.erase x := by
  intro _ hy; exact Finset.mem_filter.mp hy |> And.left

def compat {l : Type} [Bot l] (α : Lpofin l) (s : Finset Node) (x : Node) :=
  ∀ y ∈ s, ((α.form y).and (α.form x)).sat

mutual
  open Classical

  noncomputable def lin_rec {t : Type → Type} {α act test : Type}
    [∀ β, Preorder (t β)] [Preorder act] [Preorder test]
    [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [Nondet (t α)] [Bot (t α)]
    (a : Lpofin (Label act test)) (s : Finset Node) (φ : Form Node) (st : α) : t α :=
    if next a s φ = ∅ then
      pure st
    else
      Nondet.nondet fun x : ↑(next a s φ) =>
        lin_node a s φ x.val (Finset.mem_filter.mp x.property).2.1 st
    termination_by (s.card, 1)

  noncomputable def lin_node {t : Type → Type} {α act test: Type}
      [∀ β, Preorder (t β)] [Preorder act] [Preorder test]
      [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [Nondet (t α)] [Bot (t α)]
      (a : Lpofin (Label act test)) (s : Finset Node) (φ : Form Node) (x : Node) (_hx : x ∈ s)
      (st : α) : t α :=
    match a.lab x with
    | Label.bot => ⊥
    | Label.fork =>
      lin_rec a (s.erase x) φ st
    | Label.act ac =>
      bind (Sem.sem ac st) (lin_rec a (s.erase x) φ)
    | Label.test b =>
        bind (Sem.sem b st)
          fun (r : Bool) =>
            lin_rec a (filter_by_outcome a s x r)
              (φ.and (if r then Form.literal x else (Form.literal x).not))
              st
  termination_by (s.card, 0)
  decreasing_by all_goals
  · left; apply Finset.card_lt_card
    refine ssubset_of_subset_of_ssubset ?_ (Finset.erase_ssubset _hx)
    try trivial
    try exact filter_by_outcome_sub_erase
end

noncomputable def lin {t : Type → Type} {α act test : Type}
    [∀ β, Preorder (t β)] [Preorder act] [Preorder test]
    [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [Nondet (t α)] [Bot (t α)]
    (a : Lpofin (Label act test)) : α → t α :=
  lin_rec a a.nodes_finset Form.true

open Classical in
lemma next_iso {l : Type} [Bot l] [LE l] {s : Finset Node} {a b : Lpofin l} {φ : Form Node}
    (hle : a ≤ b)
    (hbot : ∀ x ∈ s, x ∈ a.nodes ∨ ∃ z ∈ a.val.bots, z ∈ s ∧ b.rel z x) :
    next a (s ∩ a.nodes_finset) φ = next b s φ := by
  ext x; constructor
  · intro h; have ⟨hxa, hx, himp, hr⟩ := Finset.mem_filter.mp h
    have hxb : x ∈ b.nodes_finset := Lpofin.le_nodes hle hxa
    refine Finset.mem_filter.mpr ⟨hxb, Finset.inter_subset_left hx, ?_, fun y hy hc => ?_⟩
    · intro v hv; exact le_form hle _ <| himp _ hv
    · have hxa := (Set.Finite.mem_toFinset _).1 hxa
      have hya := hle.downcl _ hxa y hy
      unfold Lpofin.rel at hy
      refine hr y ((hle.rel _ hya _ hxa).mpr hy) ?_
      refine Finset.mem_inter.mpr ⟨hc, ?_⟩; exact a.property.mem_toFinset.mpr hya
  · intro h; have ⟨hxb, hx, himp, hr⟩ := Finset.mem_filter.mp h
    apply Finset.mem_filter.mpr
    rcases hbot x hx with hxa | ⟨z, ⟨_, _⟩, ⟨hzs, hrel⟩⟩
    · apply a.property.mem_toFinset.mpr at hxa
      refine ⟨hxa, ?_, ?_, ?_⟩
      · exact Finset.mem_inter.mpr ⟨hx, hxa⟩
      · intro v hv; refine (congrFun (hle.form x ?_) _).mpr <| himp _ hv
        exact a.property.mem_toFinset.mp hxa
      · intro y hrel hy; apply hr _ (le_rel hle hrel)
        exact (Finset.mem_inter.mp hy).1
    · exfalso; exact hr _ hrel hzs

open Classical in
lemma lin_node_mono {m : Type → Type} {α act test : Type}
    [∀ β, OmegaCompletePartialOrder (m β)] [∀ β, OrderBot (m β)]
    [Linearizable m α]
    [Preorder act] [Sem act α (m α)]
    [Preorder test] [Sem test α (m Bool)]
    {s : Finset Node} {φ : Form Node} {a b : Lpofin (Label act test)}
    (hbot : ∀ x ∈ s, x ∈ a.nodes ∨ ∃ z ∈ a.val.bots, z ∈ s ∧ b.rel z x)
    (hle : a ≤ b)
    {x : Node} (hx : x ∈ s ∩ a.nodes_finset) (hxn : x ∈ next a (s ∩ a.nodes_finset) φ)
    {σ : α}
    (ih : ∀ {t ψ},
      t ⊆ s.erase x →
      (∀ x ∈ t, x ∈ a.nodes ∨ ∃ z ∈ a.val.bots, z ∈ t ∧ b.rel z x) →
      (lin_rec a (t ∩ a.nodes_finset) ψ : α → m α) ≤ lin_rec b t ψ) :
    (lin_node a (s ∩ a.nodes_finset) φ x hx σ : m α) ≤
    lin_node b s φ x (Finset.inter_subset_left hx) σ := by
  unfold lin_node
  have ih' (h : a.lab x ≠ ⊥) :
      (lin_rec a (s.erase x ∩ a.nodes_finset) φ : α → m α) ≤
      lin_rec b (s.erase x) φ := by
    refine ih (le_refl <| s.erase x) ?_
    intro y hy; have ⟨hne, hy⟩ := Finset.mem_erase.mp hy
    rcases hbot _ hy with hya | ⟨z, hz, hzs, hrel⟩
    · left; exact hya
    · right; refine ⟨z, hz, Finset.mem_erase.mpr ⟨?_, hzs⟩, hrel⟩
      rintro rfl; exact h hz.2
  match hl : a.lab x with
  | Label.bot => exact bot_le
  | Label.fork =>
    have hlb := lab_is_fork_le <| le_of_eq_of_le hl.symm <| hle.lab x
    conv => rhs; arg 2; exact hlb
    simp only; rw [← Finset.erase_inter]
    apply ih'; rw [hl]; intro hc; contradiction
  | Label.act ac =>
    have ⟨ac', hlb, hale⟩ := lab_is_act_le <| le_of_eq_of_le hl.symm <| hle.lab x
    conv => rhs; arg 2; exact hlb
    refine ContinuousMonad.bind_mono (Sem.sem_mono hale _) ?_
    rw [← Finset.erase_inter]; intro τ
    apply ih'; rw [hl]; intro hc; contradiction
  | Label.test bb =>
    have ⟨bb', hlb, hble⟩ := lab_is_test_le <| le_of_eq_of_le hl.symm <| hle.lab x
    conv => rhs; arg 2; exact hlb
    refine ContinuousMonad.bind_mono (Sem.sem_mono hble _) ?_
    intro p; simp only; rw [filter_by_outcome_inter hle]
    refine ih ?_ ?_ σ
    · exact filter_by_outcome_sub_erase
    · intro y hy; have ⟨hye, ⟨v, hyf, hb⟩⟩ := Finset.mem_filter.mp hy
      have ⟨hne, hy⟩ := Finset.mem_erase.mp hye
      rcases hbot _ hy with hxa | ⟨z, hz, hzs, hrel⟩
      · left; exact hxa
      · right; refine ⟨z, hz, ?_, hrel⟩; refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_erase.mpr ⟨?_, hzs⟩; rintro rfl
          have := hz.2.symm.trans hl; contradiction
        · refine ⟨v, ?_, hb⟩
          exact (b.val.property.form _ (hz.1 |> hle.nodes)).2 _ hrel _ hyf

open Classical in
theorem lin_rec_mono {m : Type → Type} {α act test : Type}
    [∀ β, OmegaCompletePartialOrder (m β)] [∀ β, OrderBot (m β)]
    [Linearizable m α]
    [Preorder act] [Sem act α (m α)]
    [Preorder test] [Sem test α (m Bool)]
    {s : Finset Node} {φ : Form Node} {a b : Lpofin (Label act test)}
    (hbot : ∀ x ∈ s, x ∈ a.nodes ∨ ∃ z ∈ a.val.bots, z ∈ s ∧ b.rel z x)
    (hle : a ≤ b) :
    (lin_rec a (s ∩ a.nodes_finset) φ : α → m α) ≤ lin_rec b s φ := by
  induction s using Finset.strongInduction generalizing φ with
  | H s ih =>
    intro σ; unfold lin_rec
    by_cases h : a.next (s ∩ a.nodes_finset) φ = ∅
    · conv => lhs; exact if_pos h
      conv => rhs; exact if_pos (next_iso hle hbot ▸ h)
    · conv => lhs; exact if_neg h
      conv =>
        rhs; exact (if_neg (next_iso hle hbot ▸ h)).trans <| Nondet.convert (next_iso hle hbot).symm
      refine Linearizable.nondet_mono ?_; intro ⟨x, hx⟩; simp only
      have hx' := hx |> Finset.mem_filter.mp |> And.left |> a.property.mem_toFinset.mp
      apply lin_node_mono hbot hle _ hx
      intro t ψ ht; apply ih t
      refine Finset.ssubset_of_subset_of_ssubset ht <| Finset.erase_ssubset ?_
      exact (Finset.mem_filter.mp hx).2.1 |> Finset.mem_inter.mp |> And.left

theorem lin_mono {m : Type → Type} {α act test : Type}
    [∀ β, OmegaCompletePartialOrder (m β)] [∀ β, OrderBot (m β)]
    [Linearizable m α]
    [PartialOrder act] [Sem act α (m α)]
    [PartialOrder test] [Sem test α (m Bool)] :
    Monotone (lin : Lpofin (Label act test) → α → m α) := by
  intro α β hle; unfold lin
  rw [← Finset.inter_eq_right.mpr <| Lpofin.le_nodes hle]
  refine lin_rec_mono ?_ hle
  intro x hx; rcases hle.succ _ <| β.property.mem_toFinset.mp hx with hxa | ⟨z, hz, hrel⟩
  · left; exact hxa
  · right; refine ⟨z, hz, ?_, hrel⟩; refine β.property.mem_toFinset.mpr ?_
    exact hle.nodes hz.1

end Lpofin

namespace Finset

open Classical in
noncomputable def equiv_image {X Y : Set Node} (e : X ≃ Y) (s : Finset Node)
    (hs : ↑s ⊆ X) : Finset Node :=
  s.attach.map {
    toFun (x : ↑s) := (e ⟨x.val, hs x.property⟩).val
    inj' _ _ h := by
      ext; have := Subtype.val_injective h |> e.injective |> Subtype.val_inj.mpr; exact this
  }

lemma mem_equiv_image_iff {X Y : Set Node} {e : X ≃ Y} {s : Finset Node}
    {hs : ↑s ⊆ X} {y : Node} :
    y ∈ s.equiv_image e hs ↔ ∃ hy : y ∈ Y, (e.symm ⟨y, hy⟩).val ∈ s := by
  refine Iff.trans mem_map ?_; constructor
  · rintro ⟨x, _, rfl⟩; refine ⟨Subtype.coe_prop _, ?_⟩
    conv => rhs; arg 1; exact e.symm_apply_apply _
    exact x.property
  · intro ⟨hy, hy'⟩; refine ⟨⟨_, hy'⟩, mem_attach _ _, ?_⟩
    have := e.apply_symm_apply ⟨_, hy⟩ |> Subtype.ext_iff.mp; exact this

lemma mem_equiv_image {X Y : Set Node} {e : X ≃ Y} {s : Finset Node}
    {hs : ↑s ⊆ X} {x : Node} (hx : x ∈ s) :
    (e ⟨x, hs hx⟩).val ∈ equiv_image e s hs := by
  refine mem_equiv_image_iff.mpr ⟨Subtype.coe_prop _, ?_⟩
  conv => rhs; arg 1; exact e.symm_apply_apply _
  exact hx

lemma equiv_image_erase {X Y : Set Node} {e : X ≃ Y} {s : Finset Node}
    {hs : ↑s ⊆ X} {x : Node} (hx : x ∈ s) :
    (s.equiv_image e hs).erase (e ⟨x, hs hx⟩).val =
    (s.erase x).equiv_image e
      (fun _ h ↦ Finset.erase_subset _ _ h |> hs) := by
  ext y; rw [mem_erase, mem_equiv_image_iff, mem_equiv_image_iff]
  constructor
  · intro ⟨hne, hy, hys⟩; refine ⟨hy, mem_erase.mpr ⟨?_, hys⟩⟩
    rintro rfl; apply hne; conv => rhs; arg 1; exact e.apply_symm_apply _
  · intro ⟨hy, he⟩; have ⟨hne, hys⟩ := mem_erase.mp he
    refine ⟨?_, hy, hys⟩
    rintro rfl; apply hne; conv => lhs; arg 1; exact e.symm_apply_apply _

end Finset

namespace Lpofin

open Linearization

open Classical in
def next_equiv {l : Type} [Bot l] {a : Lpofin l} {Y : Set Node} {e : a.nodes ≃ Y} {s : Finset Node}
    {φ : Form Node} {hs : ↑s ⊆ a.nodes} (hdep : φ.DependsOn a.nodes) :
    next a s φ ≃ next (a.permute e) (s.equiv_image e hs) (φ.permute e) := {
  toFun x := by
    refine ⟨e ⟨x.val, ?_⟩, ?_⟩ <;>
      have ⟨hxa, hxs, himp, h⟩ := Finset.mem_filter.mp x.property
    · exact a.property.mem_toFinset.mp hxa
    · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_, ?_⟩
      · refine (Set.Finite.mem_toFinset _).mpr ?_; exact Subtype.coe_prop _
      · exact Finset.mem_equiv_image hxs
      · exact (form_imp_permute _ hdep).mp himp
      · intro y ⟨hy, _, hrel⟩ hc
        have ⟨_, hys⟩ := Finset.mem_equiv_image_iff.mp hc
        conv at hrel => arg 3; arg 1; exact e.symm_apply_apply _
        exact h _ hrel hys
  invFun y := by
    refine ⟨e.symm ⟨y.val, ?_⟩, ?_⟩ <;>
      have ⟨hya, hys, himp, h⟩ := Finset.mem_filter.mp y.property
    · exact (Set.Finite.mem_toFinset _).mp hya
    · have ⟨hy, hy'⟩ := s.mem_equiv_image_iff.mp hys
      refine Finset.mem_filter.mpr ⟨?_, hy', ?_, ?_⟩
      · exact (Set.Finite.mem_toFinset _).mpr <| Subtype.coe_prop _
      · refine (form_imp_permute ?_ hdep (e := e)).mpr ?_
        · exact Subtype.prop _
        · simpa only [Subtype.coe_eta, Equiv.apply_symm_apply]
      · intro z hrel hc; refine h (e ⟨z, hs hc⟩) ⟨?_, hy, ?_⟩ ?_
        · exact Subtype.coe_prop _
        · conv => arg 2; arg 1; exact e.symm_apply_apply _
          exact hrel
        · exact s.mem_equiv_image hc
  left_inv x := by simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
  right_inv x := by simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
}

open Classical in
lemma filter_by_outcome_equiv_image {l : Type} [Bot l]
    {α : Lpofin l} {Y : Set Node} {s : Finset Node} {x : Node} {b : Bool} {e : α.nodes ≃ Y}
    {hs : ↑s ⊆ α.nodes} (hx : x ∈ s) :
    filter_by_outcome (α.permute e) (s.equiv_image e hs) (e ⟨x, hs hx⟩).val b =
    (filter_by_outcome α s x b).equiv_image e
      (fun _ h ↦ filter_by_outcome_sub_erase h |> Finset.erase_subset _ _ |> hs) := by
  ext y
  simp only [filter_by_outcome, Finset.mem_equiv_image_iff, Finset.mem_erase, Finset.mem_filter]
  constructor
  · intro ⟨⟨hne, hy, hys⟩, v, ⟨_,  hf⟩, hb⟩
    refine ⟨hy, ⟨?_, hys⟩, ?_⟩
    · rintro rfl; apply hne; conv => rhs; arg 1; exact e.apply_symm_apply _
    · refine ⟨_, hf, ?_⟩; match b with
      | true =>
        simp_all only [cond_true]; refine ⟨_, ?_, hb⟩
        conv => lhs; arg 1; exact e.symm_apply_apply _
      | false =>
        simp_all only [cond_false]; rintro ⟨z, rfl, hc⟩; apply hb
        conv => arg 1; arg 1; exact e.apply_symm_apply _
        exact hc
  · intro ⟨hy, ⟨hne, hys⟩, v, hf, hb⟩
    refine ⟨⟨?_, hy, hys⟩, ?_⟩
    · rintro rfl; apply hne; conv => lhs; arg 1; exact e.symm_apply_apply _
    · have := (Lpo.permute_form_sat_iff (e := e) (Subtype.coe_prop _)).mp hf
      conv at this => arg 2; arg 1; exact e.apply_symm_apply _
      refine ⟨_, this, ?_⟩; match b with
      | true =>
        simp_all only [cond_true]; exact ⟨_, rfl, hb⟩
      | false =>
        simp_all only [cond_false]; intro ⟨z, heq, hv⟩; apply hb
        obtain rfl := Subtype.val_injective heq |> e.injective; exact hv

lemma form_extend_equiv {l : Type} [Bot l]
    {α : Lpofin l} {Y : Set Node} {x : Node} (e : α.nodes ≃ Y) (φ : Form Node)
    (hx : x ∈ α.nodes) (r : Bool) :
    (φ.permute e).and
      (if r = true then Form.literal (e ⟨x, hx⟩).val else (Form.literal (e ⟨x, hx⟩).val).not) =
    (φ.and (if r = true then Form.literal x else (Form.literal x).not)).permute e := by
  ext v; refine and_congr (Iff.refl _) ?_
  cases r <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor
  · rintro h ⟨y, rfl, hy⟩; apply h
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply]; exact hy
  · rintro h hv; apply h; refine ⟨(e ⟨x, hx⟩), ?_, hv⟩; simp only [Equiv.symm_apply_apply]
  · intro hv; refine ⟨(e ⟨x, hx⟩), ?_, hv⟩; simp only [Equiv.symm_apply_apply]
  · rintro ⟨y, rfl, hy⟩; simp only [Subtype.coe_eta, Equiv.apply_symm_apply]; exact hy

lemma lin_node_isomorphic {m : Type → Type} {α act test : Type}
    [∀ β, OmegaCompletePartialOrder (m β)] [∀ β, OrderBot (m β)] [Linearizable m α]
    [Preorder act] [Sem act α (m α)]
    [Preorder test] [Sem test α (m Bool)]
    {X : Set Node} {φ : Form Node}
    {a : Lpofin (Label act test)} {e : a.nodes ≃ X} {s : Finset Node}
    (hs : ↑s ⊆ a.nodes) (hφ : φ.DependsOn a.nodes) {x : Node} (hx : x ∈ s)
    (ih : ∀ {t ψ} (ht : t ⊂ s),
      ψ.DependsOn a.nodes →
      (a.lin_rec t ψ : α → m α) =
      (a.permute e).lin_rec
        (Finset.equiv_image e t (fun _ h ↦ ht.subset h |> hs))
        (ψ.permute e)) :
    (lin_node a s φ x hx : α → m α) =
    lin_node (a.permute e) (s.equiv_image e hs) (φ.permute e)
      (e ⟨x, hs hx⟩).val
      (s.mem_equiv_image hx) := by
  ext σ; simp only [lin_node]
  have : (a.permute e).lab (e ⟨x, hs hx⟩).val = a.lab x := by
    refine (dif_pos (Subtype.coe_prop _)).trans ?_
    conv => lhs; arg 2; arg 1; exact e.symm_apply_apply _
    rfl
  rw [this]
  match a.lab x with
  | Label.bot => rfl
  | Label.fork =>
    simp only; rw [Finset.equiv_image_erase hx]
    refine congrFun (ih ?_ hφ) _; exact Finset.erase_ssubset hx
  | Label.act aa =>
    simp only; refine congrArg₂ _ rfl ?_; rw [Finset.equiv_image_erase hx]
    refine ih ?_ hφ; exact Finset.erase_ssubset hx
  | Label.test bb =>
    simp only; refine congrArg₂ _ rfl ?_; ext r
    rw [filter_by_outcome_equiv_image hx, form_extend_equiv e φ (hs hx) r]
    refine congrFun (ih ?_ ?_) _
    · exact ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase (Finset.erase_ssubset hx)
    · rw [← Set.union_self a.nodes]; apply Form.DependsOn.and hφ
      apply Form.DependsOn.monotone _ (Set.singleton_subset_iff.mpr <| hs hx)
      cases r <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact Form.DependsOn.literal.not
      · exact Form.DependsOn.literal

lemma lin_rec_isomorphic {m : Type → Type} {α act test : Type}
    [∀ β, OmegaCompletePartialOrder (m β)] [∀ β, OrderBot (m β)] [Linearizable m α]
    [Preorder act] [Sem act α (m α)]
    [Preorder test] [Sem test α (m Bool)]
    {X : Set Node} {φ : Form Node}
    {a : Lpofin (Label act test)} (e : a.nodes ≃ X) {s : Finset Node}
    (hs : ↑s ⊆ a.nodes) (hφ : φ.DependsOn a.nodes) :
    (lin_rec a s φ : α → m α) =
    lin_rec (a.permute e) (s.equiv_image e hs) (φ.permute e) := by
  induction s using Finset.strongInduction generalizing φ with
  | H s ih =>
    ext σ; unfold lin_rec; refine if_congr ?_ rfl ?_
    · rw [← Finset.card_eq_zero, ← Finset.card_eq_zero]
      rw [Finset.card_eq_of_equiv (next_equiv hφ)]
    · refine Nondet.nondet_congr (next_equiv hφ) ?_
      ext ⟨x, hx⟩
      refine congrFun (lin_node_isomorphic hs hφ _ ?_) _
      intro t ψ ht; apply ih t ht

lemma lin_isomorphic {m : Type → Type} {α act test : Type}
    [∀ β, OmegaCompletePartialOrder (m β)] [∀ β, OrderBot (m β)] [Linearizable m α]
    [Preorder act] [Sem act α (m α)]
    [Preorder test] [Sem test α (m Bool)]
    {a b : Lpofin (Label act test)} (h : a ≈ b) :
    (lin a : α →  m α) = lin b := by
  unfold lin; have ⟨e, h⟩ := h
  refine (lin_rec_isomorphic e ?_ ?_).trans ?_
  · conv => lhs; exact a.property.coe_toFinset
    exact subset_refl _
  · exact Form.DependsOn.monotone _ (Set.empty_subset _) Form.DependsOn.true
  · congr
    · exact Subtype.ext h
    · ext x; rw [Finset.mem_equiv_image_iff]; constructor
      · intro ⟨hx, _⟩; exact b.property.mem_toFinset.mpr hx
      · intro hx; refine ⟨b.property.mem_toFinset.mp hx, ?_⟩
        exact a.property.mem_toFinset.mpr <| Subtype.coe_prop _

end Lpofin
