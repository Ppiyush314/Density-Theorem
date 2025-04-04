import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Cones

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory Category Limits


universe u

-- C is a category with objects and Hom classes of Type u.
variable (C : Type u) [Category.{u} C]

variable{C}

/--
Defining the covariant functor Hom(A,_) from C to the category of Sets,
where A is a fixed object in C.
-/
@[simps]
def Hom_Functor (A : C) : C ⥤ Type u where

  -- Maps object X in C to the set Hom(A,X)
  obj := fun X  => A ⟶ X

  -- For objects X and Y in C, it gives a function from Hom(X,Y) to Hom(Hom(A,X), Hom(A,Y)) defined as,
  -- (f : X ⟶ Y) goes to the map taking (g : A ⟶ X) to (g ≫ f : A ⟶ Y)
  map := fun f => fun g => g ≫ f


/--
y is the Yoneda embedding, going from Cᵒᵖ to Fun(C, Sets).
-/
@[simps]
def y : Cᵒᵖ ⥤ (C ⥤ Type u) where

  -- Maps object A in Cᵒᵖ to the functor Hom(A,_)
  obj := fun A => Hom_Functor (A.unop)

  -- For A and B in Cᵒᵖ, y gives a map from Hom(B, A) to Hom(Hom(B, _), Hom(A, _)) defined as,
  -- (f : B ⟶ A) goes to the natural transformation η : Hom(B, _) ⟶ Hom(A, _), where η.app X is the map
  -- taking (g : B ⟶ X) to (f ≫ g).
  -- Note: this makes sense if you remember that in C, f goes from A to B.
  map := fun {B A} f => {

    -- Defining each component as specified above
    app := fun X => fun g => f.unop ≫ g

    -- Proving that this is a natural transformation.
    -- Just unravel the def of Hom(B, _) and Hom(A, _) and use associativity
    naturality := by

     intro U V f1
     ext h

     simp only [types_comp_apply]

     have p1 : (Hom_Functor B.unop).map f1 h = h ≫ f1 := rfl
     have p2 : (Hom_Functor A.unop).map f1 (f.unop ≫ h) = (f.unop ≫ h) ≫ f1 := rfl
     rw [p1, p2, assoc f.unop h f1]

  }


/--
Now, Yoneda's Lemma states that this functor y is fully faithful, i.e.
For any A and B in Cᵒᵖ the map from Hom(B, A) to Hom(Hom(B, _), Hom(A, _)) is bijective.
For any fixed A and B, we will show this by constructing an inverse.
-/
@[simps]
def Yoneda_bij (B A : Cᵒᵖ) : (B ⟶ A) ≅ (y.obj B ⟶ y.obj A) := {

  -- The map from Hom(B, A) to Hom(Hom(B, _), Hom(A, _)) is given by ψ
  hom := fun f => y.map f

  -- The inverse is defined as follows:
  -- For any natural transformation η from Hom(B, _) to Hom(A, _), map it to (η.app B)(𝟙 B).
  inv := fun η => (η.app B.unop (𝟙 B.unop)).op

  -- Showing hom ≫ inv is the identity on Hom(B, A).
  -- Just need to unravel the def of ψ(g).app B, which is a function from Hom(B, B) to Hom(A, B),
  -- and apply it at 𝟙 B.
  hom_inv_id := by

   ext g

   simp only [types_comp_apply, types_id_apply]

   have q1 : (y.map g).app B.unop = fun h => g.unop ≫ h := rfl
   rw [q1]

   simp

  -- Showing inv ≫ hom is the identity on Hom(Hom(B, _), Hom(A, _)).
  -- Just need to unravel the def of the natural transformation ψ(η.app B (𝟙 B)), where η is in Hom(Hom(B, _), Hom(A, _)).
  -- Then show it is the same as η by showing they give the same morphism for all X in C.
  inv_hom_id := by

   ext η X a

   simp only [types_comp_apply, types_id_apply]

   have q2 : (y.map (η.app B.unop (𝟙 B.unop)).op).app X = fun g => η.app B.unop (𝟙 B.unop) ≫ g := rfl
   rw [q2]

   simp

}


/--
Using Yoneda_bij to show y is full.
-/
@[simps]
def Yoneda_Full : Full (y : Cᵒᵖ ⥤ (C ⥤ Type u)) := {

  preimage := fun {A B : Cᵒᵖ} {α : y.obj A ⟶ y.obj B} => (Yoneda_bij A B).inv α

}

/--
Using Yoneda_bij to show y is faithful.
-/
theorem Yoneda_Faithful : Faithful (y : Cᵒᵖ ⥤ (C ⥤ Type u)) := {

  map_injective := by

    intro X Y
    rw [Function.Injective]
    intro f1 f2 h

    have p1 : (Yoneda_bij X Y).inv (y.map f1) = (Yoneda_bij X Y).inv (y.map f2) := congrArg (Yoneda_bij X Y).inv h

    have p2 : (Yoneda_bij X Y).inv ((Yoneda_bij X Y).hom f1) = f1 := hom_inv_id_apply (Yoneda_bij X Y) f1
    have p3 : (Yoneda_bij X Y).hom f1 = y.map f1 := rfl
    rw [p3] at p2
    rw [p2] at p1

    have p4 : (Yoneda_bij X Y).inv ((Yoneda_bij X Y).hom f2) = f2 := hom_inv_id_apply (Yoneda_bij X Y) f2
    have p5 : (Yoneda_bij X Y).hom f2 = y.map f2 := rfl
    rw [p5] at p4
    rw [p4] at p1

    exact p1

}


-- The above was a refinement of Project 2.
-- The goal of this section is to show that (P : C ⥤ Type u) is the co-limit of A ≫ y, for some functor A.
-- This is the well known and extremely useful result sometimes known as the Density Theorem.
-- Interestingly, the following proof does not use Yoneda's Lemma.

-- Functor from C to Type u
variable (P : C ⥤ Type u)


/--
There is a projection functor π : P.Elements ⥤ C, defined as (C, p) goes to C.
A is defined as the obvious modification of π going from P.Elementsᵒᵖ to Cᵒᵖ.
-/
@[simps]
def A : P.Elementsᵒᵖ ⥤ Cᵒᵖ where

    obj := fun X => Opposite.op (X.unop).1

    map := fun f => Opposite.op (f.unop).val



/--
The functor F is defined as the composition of A and the Yoneda embedding y.
-/
@[simps!]
def F : P.Elementsᵒᵖ ⥤ (C ⥤ Type u) := (A P) ⋙ y


-- Now we will show that P is the colimit of F.

/--
To do this we need a tuple (P, φ), where for each object X = (C, p) in P.Elementsᵒᵖ,
the natural transformation φ_X : F(X) = Hom(C,_) ⟶ P, is defined as follows:
for all B ∈ obj(C), define (φ_X)_B : Hom(C,B) ⟶ P(B) as f goes to P(f)(p).
-/
@[simps]
def φ (X : P.Elementsᵒᵖ) : (F P).obj X ⟶ P where

    -- Defined as above.
    app := fun B => fun f => (P.map f) (X.unop).2

    -- Follows easily by unfolding definitions and using the fact that P is a functor.
    naturality := by

      intro D E g
      ext f

      simp only [types_comp_apply]

      have p1 : (((F P).obj X).map g f) = f ≫ g := rfl
      rw [p1, Functor.map_comp P f g]
      rfl


-- First, we claim that (P, φ) is co-cone of F.
-- That is, for every u : Y ⟶ X in P.Elementsᵒᵖ, we have F(u) ≫ φ_X = φ_Y.

/--
Using Lean's in-built co-cone structure we show that (P,φ) is a co-cone of F.
-/
@[simps]
def CoconePφ : Cocone (F P) where

  pt := P -- Apex object P.

  -- Natural transformation ι : F ⟶ P_c, such that for all X in P.Elementsᵒᵖ, ι.app X = φ_X.
  -- Here P_c is the constant functor mapping to P.
  -- The naturality of ι is equivalent to co-cone condition for (P,φ).
  ι := {

    app := (φ P)

    -- Follows by unfolding definitions, using the fact that P is a functor, and using the fact that
    -- for all v : (A,x) ⟶ (B,y) in P.Elements, P(v)(x) = y.
    naturality := by

      intro Y X v
      simp only [Functor.const_obj_obj, Functor.const_obj_map, comp_id]

      have q1 : (F P).map v = y.map ((v.unop).val).op := rfl
      rw [q1]

      ext B q2
      simp only [FunctorToTypes.comp]

      have q3 : (y.map ((v.unop).val).op).app B = fun f => (v.unop).val ≫ f := rfl
      have q4 : (φ P X).app B = fun f => (P.map f) (X.unop).2 := rfl
      have q5 : (φ P Y).app B = fun f => (P.map f) (Y.unop).2 := rfl
      rw [q3, q4, q5]

      simp only [FunctorToTypes.map_comp_apply]
      have q6 : P.map (v.unop).val (X.unop).2 = (Y.unop).2 := ↑v.unop.2
      rw [q6]

    }


/--
Lemma L1 will need while defining the co-limit object.
It states that for g : A ⟶ B, and co-cone s = (N, ψ) of F, we have:
N(g)(ψ_(A,x))_A (𝟙 A) = (ψ_(A,x))_B (𝟙 A ≫ g), where x ∈ P(A).
This follows by unfolding definitions and from the naturality of ψ_X : F(X) ⟶ N, for all X ∈ P.Elementsᵒᵖ.
-/
lemma L1 (A B : C) (g : A ⟶ B) (s : Cocone (F P)) (x : (CoconePφ P).pt.obj A) :
    s.pt.map g ((s.ι.app (Opposite.op { fst := A, snd := x })).app A (𝟙 A)) =
    (s.ι.app (Opposite.op { fst := A, snd := x })).app B (𝟙 A ≫ g) := by

  simp only [Functor.const_obj_obj]

  let X : P.Elementsᵒᵖ := Opposite.op { fst := A, snd := x }
  let ψ_X := s.ι.app X

  have p1 : (ψ_X.app A) ≫ s.pt.map g = ((F P).obj X).map g ≫ (ψ_X.app B) := (NatTrans.naturality ψ_X g).symm

  have p2 : ((F P).obj X).map g = fun f => f ≫ g := rfl
  have p3 : (ψ_X.app A ≫ s.pt.map g) (𝟙 A) = (((F P).obj X).map g ≫ ψ_X.app B) (𝟙 A) := congrFun p1 (𝟙 A)
  rw [p2] at p3

  have p4 : s.pt.map g (ψ_X.app A (𝟙 A)) = (ψ_X.app B) (𝟙 A ≫ g) := p3
  exact p4

  done


/--
Lemma L2 we will need while defining the co-limit object.
It states that for g : A ⟶ B, and co-cone s = (N, ψ) of F, we have:
(ψ_Y)_B (𝟙 B) = (ψ_X)_B (g ≫ 𝟙 B), where X = (A,x), Y = (B,y), and y = P(g)(x).
This follows by unfolding definitions and from the fact that (N, ψ) is a co-cone of F.
-/
lemma L2 (A B : C) (g : A ⟶ B) (s : Cocone (F P)) (x : (CoconePφ P).pt.obj A) :
    (s.ι.app (Opposite.op { fst := B, snd := (CoconePφ P).pt.map g x })).app B (𝟙 B) =
    (s.ι.app (Opposite.op { fst := A, snd := x })).app B (g ≫ 𝟙 B) := by

  simp only [Functor.const_obj_obj]

  let X : P.Elementsᵒᵖ := Opposite.op { fst := A, snd := x }
  let y := (CoconePφ P).pt.map g x
  let Y : P.Elementsᵒᵖ := Opposite.op { fst := B, snd := y }
  let ψ_X := s.ι.app X
  let ψ_Y := s.ι.app Y

  have h : P.map g x = y := rfl
  let G : X.unop ⟶ Y.unop := ⟨g, h⟩

  have t1 : (F P).map (Opposite.op G) ≫ ψ_X = ψ_Y := Cocone.w s (Opposite.op G)

  have t2 : ((F P).map (Opposite.op G) ≫ ψ_X).app B = ψ_Y.app B := congrFun (congrArg NatTrans.app t1) B
  have t5 : (((F P).map (Opposite.op G)).app B ≫ ψ_X.app B) (𝟙 B) = ψ_Y.app B (𝟙 B) := congrFun t2 (𝟙 B)

  have t7 : ψ_X.app B (g ≫ (𝟙 B)) = ψ_Y.app B (𝟙 B) := t5
  exact id t7.symm

  done


/--
Lemma L3 we will need while defining the co-limit object. It is just a slightly different version of lemma L2.
-/
lemma L3 (s : Cocone (F P)) (X : P.Elementsᵒᵖ) (B : C) (f : ((F P).obj X).obj B) :
    (s.ι.app (Opposite.op { fst := B, snd := ((CoconePφ P).ι.app X).app B f })).app B (𝟙 B) =
    (s.ι.app X).app B (f ≫ 𝟙 B) := by

  simp only [Functor.const_obj_obj]
  exact L2 P (X.unop.1) B f s (X.unop.2)

  done


/--
Finally, we cliam that (P, φ) is a co-limit of F.
That is, for any co-cone s = (N,ψ) of F, there is a unique morphism u : P ⟶ N such that
for all X in P.Elementsᵒᵖ, φ_X ≫ u = ψ_X.
-/
@[simps]
def ColimitPφ : IsColimit (CoconePφ P) where

  -- Defining the natural transformation u : P ⟶ N as:
  -- u_B(x) = (ψ_(B,x))_B (𝟙 B), for all x in P(B).
  desc s := {

    app := fun B => fun x => ((s.ι).app (Opposite.op ⟨B, x⟩)).app B (𝟙 B)

    naturality := by

      intro A B g
      ext x
      simp only [Functor.const_obj_obj, types_comp_apply]

      -- From the naturality of ψ_X : F(X) ⟶ N. Proved in lemma L1.
      have q1 : s.pt.map g ((s.ι.app (Opposite.op { fst := A, snd := x })).app A (𝟙 A)) =
      (s.ι.app (Opposite.op { fst := A, snd := x })).app B (𝟙 A ≫ g) := L1 P A B g s x

      -- From the fact that (N, ψ) is a co-cone of F. Proved in lemma L2.
      have q2 : (s.ι.app (Opposite.op { fst := B, snd := (CoconePφ P).pt.map g x })).app B (𝟙 B) =
      (s.ι.app (Opposite.op { fst := A, snd := x })).app B (g ≫ 𝟙 B) := L2 P A B g s x

      rw [q1, q2]
      simp

  }

  -- Prove that for all X in P.Elementsᵒᵖ, φ_X ≫ u = ψ_X.
  fac := by

    intro s X
    ext B f
    simp only [Functor.const_obj_obj, FunctorToTypes.comp]

    -- From the fact that (N, ψ) is a co-cone of F. Proved in lemma L3.
    have q4 : (s.ι.app (Opposite.op { fst := B, snd := ((CoconePφ P).ι.app X).app B f })).app B (𝟙 B) =
    (s.ι.app X).app B (f ≫ 𝟙 B) := L3 P s X B f

    rw [q4]
    simp


  -- Prove that u is the unique morphism with this property.
  -- Let v : P ⟶ N be another morphism such that 'fac' holds. Claim: u = v.
  -- Follows easily from the hypothesis, and by unfolding definitions.
  uniq := by

    intro s v h1
    ext B x
    specialize h1 (Opposite.op ⟨B, x⟩)
    simp only [Functor.const_obj_obj]

    have q6 : ((CoconePφ P).ι.app (Opposite.op { fst := B, snd := x })).app B ≫ v.app B =
    (s.ι.app (Opposite.op { fst := B, snd := x })).app B := congrFun (congrArg NatTrans.app h1) B

    have q8 :  v.app B (((CoconePφ P).ι.app (Opposite.op { fst := B, snd := x })).app B (𝟙 B)) =
    (s.ι.app (Opposite.op { fst := B, snd := x })).app B (𝟙 B) := congrFun q6 (𝟙 B)

    have q9 : ((CoconePφ P).ι.app (Opposite.op { fst := B, snd := x })).app B (𝟙 B) =
    P.map (𝟙 B) x := rfl

    have q10 : P.map (𝟙 B) x = (𝟙 P.obj B) x := FunctorToTypes.map_id_apply P x

    have q11 : (𝟙 P.obj B) x = x := rfl

    rw [q11] at q10
    rw [q10] at q9
    rw [q9] at q8

    exact q8
