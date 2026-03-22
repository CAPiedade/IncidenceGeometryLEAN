import Mathlib
universe u v w

/-structure IncidenceSystem (X : Type u) (I : Type v) where
  points : Set X
  types : Set I
  type_func : X → I
  incidence : X → X → Prop
  incidence_reflexive : Reflexive incidence
  incidence_symmetric : Symmetric incidence
  incidence_type_condition : ∀ {x y : X}, x ∈ points → y ∈ points→ incidence x y ↔ type_func x ≠ type_func y ∨ x=y

 /--Create a coloring  -/
def IncidenceSystemGraph (S : IncidenceSystem X I) : SimpleGraph X where
  Adj a b := a ≠ b ∧ (S.incidence a b ∨ S.incidence b a)


def FlagOfIncidenceSystem {X I} (F : Set X) (S : IncidenceSystem X I) :=  {x | x ∈ F ∧ x ∈ S.points}



def ResidueOfIncidenceSystem (S : IncidenceSystem X I) (Fl : FlagOfIncidenceSystem F S) : IncidenceSystem X I where
  points := {x | x ∈ S.points ∧ ∀ y ∈ F, S.incidence x y ∧ x ≠ y}
  types := {S.type_func x | x ∈ F}
  type_func := S.type_func
  incidence := S.incidence
  incidence_reflexive := S.incidence_reflexive
  incidence_symmetric := S.incidence_symmetric
  incidence_type_condition := S.incidence_type_condition
-/

structure IncidenceSystem (X : Type u) (I : Type v) where
  points : Set X
  types : Set I
  type_func : X → I
  incidence : X → X → Prop
  incidence_reflexive : Reflexive incidence
  incidence_symmetric : Symmetric incidence
  incidence_type_condition :
    ∀ x y : X, x ∈ points → y ∈ points → (incidence x y ↔ (type_func x ≠ type_func y ∨ x = y))

variable {X : Type u} {I : Type v}

-- elements of X \ points are singletons in this graph
def IncidenceGraph (S : IncidenceSystem X I) : SimpleGraph X where
  Adj a b := a ≠ b ∧ S.incidence a b  -- We already have symmetry in S
  symm a b := by                      -- so symmetry requires a proof
    intro ⟨hne, hab⟩                  -- suppose hne : a ≠ b and hab : S.incidence a b
    exact ⟨Ne.symm hne, S.incidence_symmetric hab⟩  -- and invoke symmetry

def IncidenceGraphColoring {S : IncidenceSystem X I} :
    (IncidenceGraph S).Coloring I := sorry






/- A flag is a set of pairwise incident elements -/
def IsFlag (F : Set X) (S : IncidenceSystem X I) : Prop :=
  F ⊆ S.points ∧ ∀ x ∈ F, ∀ y ∈ F, S.incidence x y

theorem IsFlag_iff (S : IncidenceSystem X I) (F : Set X) (hF : F ⊆ S.points) :
    IsFlag F S ↔ (IncidenceGraph S).IsClique F := by
  simp_all only [IsFlag, true_and, SimpleGraph.IsClique, IncidenceGraph, ne_eq]
  constructor
  · intro hF' a ha b hb hne
    exact ⟨hne, hF' a ha b hb⟩
  · intro h x hx y hy
    match Classical.em <| x = y with
    | Or.inl heq =>
        subst heq
        exact S.incidence_reflexive x
    | Or.inr hne => exact (h hx hy hne).right


def ResidueOfIncidenceSystem (F : Set X) (S : IncidenceSystem X I) (hF : IsFlag F S) :
    IncidenceSystem X I where
  points := {x | x ∈ S.points \ F ∧ ∀ y ∈ F, S.incidence x y}
  types := Set.image S.type_func {x | x ∈ S.points \ F ∧ ∀ y ∈ F, S.incidence x y}
  type_func := S.type_func
  incidence := S.incidence
  incidence_reflexive := S.incidence_reflexive
  incidence_symmetric := S.incidence_symmetric
  incidence_type_condition := by
    intro x y
    match Classical.em <| x = y with
    | Or.inl h =>
        subst h
        simp [S.incidence_reflexive x]
    | Or.inr h =>
        simp only [Set.mem_diff, Set.mem_setOf_eq, ne_eq, h, or_false, and_imp]
        intro hx _ _ hy _ _
        simp [h, S.incidence_type_condition x y hx hy]


theorem ResidueOfIncidenceSystem_points (F : Set X) (S : IncidenceSystem X I) (hF : IsFlag F S) :
    (ResidueOfIncidenceSystem F S hF).points ⊆ S.points := by
  simp only [ResidueOfIncidenceSystem, Set.mem_setOf_eq, Set.mem_diff, true_and, and_imp]
  intro x hx
  simp only [Set.mem_setOf_eq,] at hx
  exact hx.1.1

theorem FlagOfResidue_FlagOfOriginal (F G: Set X) (S : IncidenceSystem X I) (hF : IsFlag F S):
    IsFlag G (ResidueOfIncidenceSystem F S hF) → IsFlag G S := by
  simp only [IsFlag, ResidueOfIncidenceSystem, and_imp]
  intro hG_points hG_incidence
  exact ⟨Set.Subset.trans hG_points (ResidueOfIncidenceSystem_points F S hF),
  fun x hx y hy => hG_incidence x hx y hy⟩

theorem FlagOfResidue_iff_BigFlagOfIncidenceSystem (S : IncidenceSystem X I) (F G: Set X)
(hF : IsFlag F S) (hG : G ⊆ (ResidueOfIncidenceSystem F S hF).points):
    IsFlag G (ResidueOfIncidenceSystem F S hF) ↔ IsFlag (F ∪ G) S := by
  simp only [IsFlag, ResidueOfIncidenceSystem, Set.mem_diff, Set.union_subset_iff]
  apply Iff.intro
  · intro direct_imp
    obtain ⟨left, right⟩ := direct_imp
    apply And.intro
    · constructor
      · intro x hx
        simp [IsFlag] at hF
        exact hF.1 hx
      · intro y hy
        let k := left hy
        simp at k
        exact k.1.1
    · intro x hx y hy
      simp at hx hy
      match hx,hy with
      | Or.inl hx', Or.inl hy' => exact hF.2 x hx' y hy'
      | Or.inl hx', Or.inr hy' =>
        let k := left hy'
        simp at k
        exact S.incidence_symmetric (k.2 x hx')
      | Or.inr hx', Or.inl hy' =>
        let k := left hx'
        simp at k
        exact k.2 y hy'
      | Or.inr hx', Or.inr hy' => exact right x hx' y hy'
  · intro reverse_imp
    obtain ⟨left, right⟩ := reverse_imp
    apply And.intro
    · intro x hx
      let k := hG hx
      simp [ResidueOfIncidenceSystem] at k
      exact k
    · intro x hx y hy
      exact right x (Or.inr hx) y (Or.inr hy)

def IncSys_IsConnected (S : IncidenceSystem X I) : Prop :=
  SimpleGraph.Connected (IncidenceGraph S)

def TypeOfFlag (F : Set X) (S : IncidenceSystem X I) : Set I :=
  Set.image S.type_func F

def IsChamber (F : Set X) (S : IncidenceSystem X I) : Prop :=
  IsFlag F S ∧ (TypeOfFlag F S) = Set.image S.type_func S.points


def IncSys_IsResiduallyConnected (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) →
  IncSys_IsConnected (ResidueOfIncidenceSystem F S hF)
  ∧ Set.ncard (ResidueOfIncidenceSystem F S hF).types ≥ 2


def IsGeometry (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) → ∃ C : Set X, C ⊆ S.points ∧ IsChamber C S ∧ F ⊆ C

def IsFirm (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) → IsGeometry S →
  Set.ncard (ResidueOfIncidenceSystem F S hF).types = 1 →
  Set.ncard (ResidueOfIncidenceSystem F S hF).points ≥ 2

def IsThin (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) → IsGeometry S →
  Set.ncard (ResidueOfIncidenceSystem F S hF).types = 1 →
  Set.ncard (ResidueOfIncidenceSystem F S hF).points = 2

def IsThick (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) → IsGeometry S →
  Set.ncard (ResidueOfIncidenceSystem F S hF).types = 1 →
  Set.ncard (ResidueOfIncidenceSystem F S hF).points > 2

def IsHypertope (S : IncidenceSystem X I) : Prop :=
IsGeometry S ∧  IsThin S ∧ IncSys_IsResiduallyConnected S



def IsWeakHomomorphism (S T : IncidenceSystem X I) (α : X → X) : Prop :=
  ∀ x ∈ S.points, α x ∈ T.points ∧
  ∀ x ∈ S.points, ∀ y ∈ S.points, ((S.incidence x y → T.incidence (α x) (α y)) ∧
  (S.type_func x = S.type_func y ↔ T.type_func (α x) = T.type_func (α y)))

def IsHomomorphism (S T : IncidenceSystem X I) (α : X → X) : Prop :=
  IsWeakHomomorphism S T α ∧ S.types = T.types ∧
  ∀ x ∈ S.points, S.type_func x = T.type_func (α x)

def IsCorrelation [Nonempty X] (S T : IncidenceSystem X I) (α : X → X) : Prop :=
  IsWeakHomomorphism S T α ∧ Function.Bijective α ∧ IsWeakHomomorphism T S (Function.invFun α)

def IsIsomorphism [Nonempty X] (S T : IncidenceSystem X I) (α : X → X) : Prop :=
  IsHomomorphism S T α ∧ IsCorrelation S T α

def IsAutomorphism [Nonempty X] (S : IncidenceSystem X I) (α : X → X) : Prop :=
  IsIsomorphism S S α

def IsAutoCorrelation [Nonempty X] (S : IncidenceSystem X I) (α : X → X) : Prop :=
  IsCorrelation S S α

structure WeakHomomorphism [Nonempty X] (S T : IncidenceSystem X I) where
  Fun : X → X
  isWeakHom : IsWeakHomomorphism S T Fun

structure Homomorphism [Nonempty X] (S T : IncidenceSystem X I) extends WeakHomomorphism S T where
  isHom : IsHomomorphism S T Fun
  isWeakHom := by exact isHom.1

structure Correlation [Nonempty X] (S T : IncidenceSystem X I) extends WeakHomomorphism S T where
  isCorr : IsCorrelation S T Fun
  isWeakHom := by exact isCorr.1

structure Isomorphism [Nonempty X] (S T : IncidenceSystem X I) extends Homomorphism S T where
  isIso : IsIsomorphism S T Fun
  isHom:= by exact isIso.1

structure Automorphism [Nonempty X] (S : IncidenceSystem X I) extends Isomorphism S S where
  isAuto : IsAutomorphism S Fun := isIso

structure AutoCorrelation [Nonempty X] (S : IncidenceSystem X I) extends Correlation S S where
  isAutoCorr : IsAutoCorrelation S Fun := isCorr

def composeWeakHomomorphism [Nonempty X]
    {S T U : IncidenceSystem X I}
    (α : WeakHomomorphism S T) (β : WeakHomomorphism T U) :
    WeakHomomorphism S U :=
{ Fun := β.Fun ∘ α.Fun
  isWeakHom := by
    intro x hx
    have hαx : α.Fun x ∈ T.points := (α.isWeakHom x hx).1
    have hβx : β.Fun (α.Fun x) ∈ U.points := (β.isWeakHom (α.Fun x) hαx).1
    constructor
    · exact hβx
    · intro x hx y hy
      have hαx : α.Fun x ∈ T.points := (α.isWeakHom x hx).1
      have hαy : α.Fun y ∈ T.points := (α.isWeakHom y hy).1
      have hαxy :
          (S.incidence x y → T.incidence (α.Fun x) (α.Fun y)) ∧
          (S.type_func x = S.type_func y ↔
            T.type_func (α.Fun x) = T.type_func (α.Fun y)) :=
        (α.isWeakHom x hx).2 x hx y hy
      have hβxy :
          (T.incidence (α.Fun x) (α.Fun y) →
            U.incidence (β.Fun (α.Fun x)) (β.Fun (α.Fun y))) ∧
          (T.type_func (α.Fun x) = T.type_func (α.Fun y) ↔
            U.type_func (β.Fun (α.Fun x)) = U.type_func (β.Fun (α.Fun y))) :=
        (β.isWeakHom (α.Fun x) hαx).2 (α.Fun x) hαx (α.Fun y) hαy
      refine ⟨?_, ?_⟩
      · intro hS
        exact hβxy.1 (hαxy.1 hS)
      · exact Iff.trans hαxy.2 hβxy.2
}

def composeHomomorphism [Nonempty X]
    {S T U : IncidenceSystem X I}
    (α : Homomorphism S T) (β : Homomorphism T U) :
    Homomorphism S U :=
{ toWeakHomomorphism := composeWeakHomomorphism α.toWeakHomomorphism β.toWeakHomomorphism
  isHom := by
    constructor
    · exact (composeWeakHomomorphism α.toWeakHomomorphism β.toWeakHomomorphism).isWeakHom
    · constructor
      · calc S.types = T.types := α.isHom.2.1
          _ = U.types := β.isHom.2.1
      · intro x hx
        calc S.type_func x = T.type_func (α.Fun x) := α.isHom.2.2 x hx
          _ = U.type_func (β.Fun (α.Fun x)) := β.isHom.2.2 (α.Fun x) ((α.isWeakHom x hx).1)
}

def composeCorrelation [Nonempty X]
    {S T U : IncidenceSystem X I}
    (α : Correlation S T) (β : Correlation T U) :
    Correlation S U :=
{ toWeakHomomorphism := composeWeakHomomorphism α.toWeakHomomorphism β.toWeakHomomorphism
  isCorr := by
    constructor
    · exact (composeWeakHomomorphism α.toWeakHomomorphism β.toWeakHomomorphism).isWeakHom
    · constructor
      · exact Function.Bijective.comp β.isCorr.2.1 α.isCorr.2.1
      · sorry  -- composition of inverse weak homomorphisms
}

def composeIsomorphism [Nonempty X]
    {S T U : IncidenceSystem X I}
    (α : Isomorphism S T) (β : Isomorphism T U) :
    Isomorphism S U :=
{ toHomomorphism := composeHomomorphism α.toHomomorphism β.toHomomorphism
  isIso := by
    constructor
    · exact (composeHomomorphism α.toHomomorphism β.toHomomorphism).isHom
    · constructor
      · exact (composeHomomorphism α.toHomomorphism β.toHomomorphism).isHom.1
      · constructor
        · exact Function.Bijective.comp β.isIso.2.2.1 α.isIso.2.2.1
        · sorry  -- composition of inverse weak homomorphisms
}

def composeAutomorphism [Nonempty X]
    {S : IncidenceSystem X I}
    (α β : Automorphism S) :
    Automorphism S :=
{ toIsomorphism := composeIsomorphism α.toIsomorphism β.toIsomorphism
  isAuto := (composeIsomorphism α.toIsomorphism β.toIsomorphism).isIso
}

def composeAutoCorrelation [Nonempty X]
    {S : IncidenceSystem X I}
    (α β : AutoCorrelation S) :
    AutoCorrelation S :=
{ toCorrelation := composeCorrelation α.toCorrelation β.toCorrelation
  isAutoCorr := (composeCorrelation α.toCorrelation β.toCorrelation).isCorr
}

-- The automorphism group is a subgroup of the permutation group
instance IncSys_AutomorphismGroup [Nonempty X] (S : IncidenceSystem X I) : Group (Automorphism S) :=
  { mul := fun α β => sorrry
    one := id
    inv := fun α => Function.invFun (α : X → X)
    mul_assoc := by
      intros α β γ
      ext x
      simp [Function.comp]
    one_mul := by
      intro α
      ext x
      simp [Function.comp, id]
    mul_one := by
      intro α
      ext x
      simp [Function.comp, id]
    mul_left_inv := by
      intro α
      ext x
      simp [Function.comp, Function.invFun] }
