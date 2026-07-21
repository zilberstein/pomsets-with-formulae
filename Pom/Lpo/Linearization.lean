import Pom.Lpo.Basic
import Pom.Lpo.Order
import Pom.Lpo.Order.FinApprox
import Pom.Lpo.Isomorphism
import Pom.Lpo.Linearization.Label

namespace Linearization

class Nondet (α : Type) where
  nondet {ι : Type} [Finite ι] : (ι → α) → α

lemma nondet_convert {α ι : Type} {X Y : Finset ι} [Nondet α]
    {f : ↑X → α} (h : X = Y) :
    Nondet.nondet f = Nondet.nondet fun x : ↑Y ↦ f ⟨x.val, by subst h; exact x.property⟩ := by
  subst h; rfl

class Sem (c : Type) (in_type out_type : Type) where
  sem : c → in_type → out_type

open OmegaCompletePartialOrder

class ContSem (c : Type) (in_type out_type : Type) [DCPO c] [DCPO out_type]
  extends Sem c in_type out_type where
  sem_mono : Monotone sem
  sem_continuous : ωScottContinuous sem

class ContinuousMonad (t : Type → Type) where
  bind_mono {α β : Type} [Monad t] [Preorder (t α)] [Preorder (t β)] :
    ∀ {m₁ m₂ : t α} {k₁ k₂ : α → t β}, m₁ ≤ m₂ → k₁ ≤ k₂ → (m₁ >>= k₁) ≤ (m₂ >>= k₂)
  bind_continuous {α β : Type} [Monad t]
    [OmegaCompletePartialOrder (t α)] [OmegaCompletePartialOrder (t β)] :
    ∀ {c₁ : Chain (t α)} {c₂ : Chain (α → t β)},
      (ωSup c₁ >>= ωSup c₂) = ωSup {
        toFun n := c₁ n >>= c₂ n
        monotone' _ _ hle := bind_mono (c₁.monotone' hle) (c₂.monotone' hle)
      }

class Linearizable (t : Type → Type) (α : Type)
  extends Monad t, ContinuousMonad t, LawfulMonad t, Nondet (t α) where
  nondet_mono {ι : Type} [Finite ι] [Preorder (t α)] : Monotone (@nondet ι _)
  nondet_continuous {ι : Type} [Finite ι] [OmegaCompletePartialOrder (t α)] :
    ωScottContinuous (@nondet ι _)

  bind_additive {ι : Type} [Finite ι] (κ : ι → t α) (f : α → t α) :
    nondet κ >>= f = nondet fun i ↦ κ i >>= f

namespace Lpofin

open Classical in
noncomputable def next {l : Type} [Bot l] (a : Lpofin l) (s : Finset Node) : Finset Node :=
  a.nodes_finset.filter fun x ↦ x ∈ s ∧ ∀ y, a.rel y x → y ∉ s

lemma next_empty {l : Type} [Bot l] {a : Lpofin l} :
    next a ∅ = ∅ := by
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

mutual
  open Classical

  noncomputable def lin_rec {t : Type → Type} {α act test : Type}
    [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [Nondet (t α)] [Bot (t α)]
    (a : Lpofin (Label act test)) (s : Finset Node) (st : α) : t α :=
    if s = ∅ then
      pure st
    else
      Nondet.nondet fun x : ↑(next a s) =>
        lin_node a s x.val (Finset.mem_filter.mp x.property).2.1 st
    termination_by (s.card, 1)

  noncomputable def lin_node {t : Type → Type} {α act test: Type}
      [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [Nondet (t α)] [Bot (t α)]
      (a : Lpofin (Label act test)) (s : Finset Node) (x : Node) (hx : x ∈ s)
      (st : α) : t α :=
    have _h : (s.erase x).card < s.card := Finset.card_erase_lt_of_mem hx
    match a.lab x with
    | Label.bot => ⊥
    | Label.fork => lin_rec a (s.erase x) st
    | Label.act ac => bind (Sem.sem ac st) (lin_rec a (s.erase x))
    | Label.test b =>
        bind (Sem.sem b st)
          fun (r : Bool) =>
            lin_rec a (filter_by_outcome a s x r) st
  termination_by (s.card, 0)
  decreasing_by
  · left; exact _h
  · left; exact _h
  · left; classical exact lt_of_lt_of_le' _h (Finset.card_filter_le _ _)
end

noncomputable def lin {t : Type → Type} {α act test : Type}
  [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [Nondet (t α)] [Bot (t α)]
  (a : Lpofin (Label act test)) : α → t α :=
    lin_rec a a.nodes_finset

open Classical in
lemma next_iso {l : Type} [Bot l] [LE l] {s : Finset Node} {a b : Lpofin l}
    (hle : a ≤ b)
    (hbot : ∀ x ∈ s, x ∈ a.nodes ∨ ∃ z ∈ a.val.bots, z ∈ s ∧ b.rel z x) :
    next a (s ∩ a.nodes_finset) = next b s := by
  ext x; constructor
  · intro h; have ⟨hxa, hx, hr⟩ := Finset.mem_filter.mp h
    have hxb : x ∈ b.nodes_finset := Lpofin.le_nodes hle hxa
    refine Finset.mem_filter.mpr ⟨hxb, Finset.inter_subset_left hx, fun y hy hc => ?_⟩
    have hxa := (Set.Finite.mem_toFinset _).1 hxa
    have hya := hle.downcl _ hxa y hy
    unfold Lpofin.rel at hy
    refine hr y ((hle.rel _ hya _ hxa).mpr hy) ?_
    refine Finset.mem_inter.mpr ⟨hc, ?_⟩; exact a.property.mem_toFinset.mpr hya
  · intro h; have ⟨hxb, hx, hr⟩ := Finset.mem_filter.mp h; apply Finset.mem_filter.mpr
    rcases hbot x hx with hxa | ⟨z, ⟨_, _⟩, ⟨hzs, hrel⟩⟩
    · apply a.property.mem_toFinset.mpr at hxa
      refine ⟨hxa, ?_, ?_⟩
      · exact Finset.mem_inter.mpr ⟨hx, hxa⟩
      · intro y hrel hy; apply hr _ (le_rel hle hrel)
        exact (Finset.mem_inter.mp hy).1
    · exfalso; exact hr _ hrel hzs

open Classical in
lemma lin_node_mono {m : Type → Type} {α act test : Type}
    [Linearizable m α] [∀ β, DCPO (m β)] [∀ β, OrderBot (m β)]
    [DCPO act] [ContSem act α (m α)]
    [DCPO test] [ContSem test α (m Bool)]
    {s : Finset Node} {a b : Lpofin (Label act test)}
    (hbot : ∀ x ∈ s, x ∈ a.nodes ∨ ∃ z ∈ a.val.bots, z ∈ s ∧ b.rel z x)
    (hle : a ≤ b)
    {x : Node} (hx : x ∈ s ∩ a.nodes_finset) (hxn : x ∈ next a (s ∩ a.nodes_finset)) {σ : α}
    (ih : ∀ {t},
      t ⊆ s.erase x →
      (∀ x ∈ t, x ∈ a.nodes ∨ ∃ z ∈ a.val.bots, z ∈ t ∧ b.rel z x) →
      (lin_rec a (t ∩ a.nodes_finset) : α → m α) ≤ lin_rec b t) :
    (lin_node a (s ∩ a.nodes_finset) x hx σ : m α) ≤
    lin_node b s x (Finset.inter_subset_left hx) σ := by
  unfold lin_node; simp only
  have ih' (h : a.lab x ≠ ⊥) :
      (lin_rec a (s.erase x ∩ a.nodes_finset) : α → m α) ≤
      lin_rec b (s.erase x) := by
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
    refine ContinuousMonad.bind_mono (ContSem.sem_mono hale _) ?_
    rw [← Finset.erase_inter]; intro τ
    apply ih'; rw [hl]; intro hc; contradiction
  | Label.test bb =>
    have ⟨bb', hlb, hble⟩ := lab_is_test_le <| le_of_eq_of_le hl.symm <| hle.lab x
    conv => rhs; arg 2; exact hlb
    refine ContinuousMonad.bind_mono (ContSem.sem_mono hble _) ?_
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
    [Linearizable m α] [∀ β, DCPO (m β)] [∀ β, OrderBot (m β)]
    [DCPO act] [ContSem act α (m α)]
    [DCPO test] [ContSem test α (m Bool)]
    {s : Finset Node} {a b : Lpofin (Label act test)}
    (hbot : ∀ x ∈ s, x ∈ a.nodes ∨ ∃ z ∈ a.val.bots, z ∈ s ∧ b.rel z x)
    (hle : a ≤ b) :
    (lin_rec a (s ∩ a.nodes_finset) : α → m α) ≤ lin_rec b s := by
  induction s using Finset.strongInduction with
  | H s ih =>
    intro σ
    have heq := next_iso hle hbot; unfold lin_rec
    by_cases h : s = ∅
    · subst h
      conv => lhs; exact if_pos <| Finset.empty_inter _
      conv => rhs; exact if_pos rfl
    · have ht_emp : s ∩ a.nodes_finset ≠ ∅ := by
        have ⟨x, hx⟩ := Finset.nonempty_of_ne_empty h
        rcases hbot _  hx with hxa | ⟨z, ⟨hza, _⟩, hz, _⟩
        · exact Finset.ne_empty_of_mem <| Finset.mem_inter.mpr ⟨hx, a.property.mem_toFinset.mpr hxa⟩
        · exact Finset.ne_empty_of_mem <| Finset.mem_inter.mpr ⟨hz, a.property.mem_toFinset.mpr hza⟩
      conv => lhs; exact if_neg ht_emp
      conv => rhs; exact (if_neg h).trans <| nondet_convert heq.symm
      refine Linearizable.nondet_mono ?_; intro ⟨x, hx⟩; simp only
      apply lin_node_mono hbot hle _ hx
      intro t ht; apply ih
      refine Finset.ssubset_of_subset_of_ssubset ht <| Finset.erase_ssubset ?_
      exact (Finset.mem_filter.mp hx).2.1 |> Finset.mem_inter.mp |> And.left

theorem lin_mono {m : Type → Type} {α act test : Type}
    [Linearizable m α] [∀ β, DCPO (m β)] [∀ β, OrderBot (m β)]
    [DCPO act] [ContSem act α (m α)]
    [DCPO test] [ContSem test α (m Bool)] :
    Monotone (lin : Lpofin (Label act test) → α → m α) := by
  intro α β hle; unfold lin
  rw [← Finset.inter_eq_right.mpr <| Lpofin.le_nodes hle]
  refine lin_rec_mono ?_ hle
  intro x hx; rcases hle.succ _ <| β.property.mem_toFinset.mp hx with hxa | ⟨z, hz, hrel⟩
  · left; exact hxa
  · right; refine ⟨z, hz, ?_, hrel⟩; refine β.property.mem_toFinset.mpr ?_
    exact hle.nodes hz.1

open Classical in
noncomputable def finset_equiv_image {X Y : Set Node} (e : X ≃ Y) (s : Finset Node) : Finset Node :=
  s.filterMap
    (fun x ↦ if hx : x ∈ X then some (e ⟨_, hx⟩).val else none)
    (by {
      simp only [Option.mem_def, Option.dite_none_right_eq_some, Option.some.injEq,
        forall_exists_index, forall_apply_eq_imp_iff]
      intro _ _ _ _ heq; symm; exact Subtype.ext_iff.mp (e.injective (Subtype.ext heq))
    })

lemma lin_rec_iso {m : Type → Type} {α act test : Type}
    [Linearizable m α] [Bot (m α)]
    [Sem act α (m α)] [Sem test α (m Bool)]
    {X : Set Node}
    {a : Lpofin (Label act test)} {e : a.nodes ≃ X} {s : Finset Node} :
    (lin_rec a s : α → m α) =
    lin_rec (a.permute e) (finset_equiv_image e s) := by
  induction s using Finset.strongInduction with
  | H s hind =>
    ext st; unfold lin_rec; by_cases h : s = ∅
    · subst h; simp only [↓reduceIte, finset_equiv_image, Finset.filterMap_empty]
    · sorry

lemma lin_iso {m : Type → Type} {α act test : Type}
    [Linearizable m α] [Bot (m α)]
    [Sem act α (m α)] [Sem test α (m Bool)]
    {a b : Lpofin (Label act test)} (h : a ≈ b) :
    (lin a : α →  m α) = lin b := by
  unfold lin; rcases h with ⟨e, h⟩
  refine Eq.trans lin_rec_iso (congr_arg₂ _ (Subtype.ext h) ?_)
  have hn := congr_arg Lpo.nodes h; simp [Lpo.permute, Lpo.nodes] at hn
  sorry
  -- have _ : Fintype ↑(e '' a.val.val.nodes) := by
  --   unfold Lpo.nodes; rw [hn]; exact b.property.fintype
  -- have _ : Fintype ↑(b.val.val.nodes) := b.property.fintype
  -- refine (@Set.Finite.toFinset_image _ _ _ ?_ _ _ ?_).symm.trans ?_
  -- · unfold Lpo.nodes; rw [hn]; exact b.property
  -- · unfold Lpofin.nodes_finset; unfold Set.Finite.toFinset
  --   refine @Set.toFinset_congr _ _ _ ?_ ?_ hn

end Lpofin

end Linearization
