module Main where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

-- Definitions
postulate 
    Point : Set 
    Line : Set
    Line-Contains-Point : Point → Line → Set

data Point= : Point → Point → Set where
  point= : ∀ {p} → Point= p p

point-refl : (p : Point) → Point= p p
point-refl _ = point=

postulate
    Point-Superpose : Point → Point → Set
    point-eq : (p1 p2 : Point) → Point-Superpose p1 p2 

record Segment : Set where
    constructor
        segment 
    field
        point1 point2 : Point

data Seg= : Segment → Segment → Set where
  seg= : ∀ {s1 s2} → Seg= s1 s2

postulate
    Line-Contains-Segment : Segment → Line → Set
    Segment= : Segment → Segment → Set
    seg-eq : (s1 s2 : Segment) → Segment= s1 s2  

seg-trans : (a b c : Segment) → Segment= a b → Segment= b c → Segment= a c
seg-trans a b c ab bc  = seg-eq a c 

seg-sym : {a b : Segment} → Segment= a b → Segment= b a 
seg-sym {a} {b} ab = seg-eq b a

seg-inverse : Segment → Segment
seg-inverse (segment a b) = segment b a


postulate
    Distance : Nat → Set 

record Angle : Set where
    constructor
        angle 
    field
        seg1 : Segment
        seg2 : Segment

postulate
    Angle= : Angle → Angle → Set
    ang-eq : (a1 a2 : Angle) → Angle= a1 a2  

data Ang= : Angle → Angle → Set where
  ang= : ∀ {a1 a2} → Ang= a1 a2
    

record Triangle : Set where
    field
        p1 p2 p3 : Point
    
    side1 : Segment
    side1 = record { point1 = p2 ; point2 = p3 }

    side2 : Segment
    side2 = record { point1 = p3 ; point2 = p1 }

    side3 : Segment
    side3 = record { point1 = p1 ; point2 = p2 }

    angle1 : Angle
    angle1 = angle side2 side3 

    angle2 : Angle
    angle2 = angle side3 side1 
    
    angle3 : Angle
    angle3 = angle side1 side2

    
record EquilTri : Set where
    constructor
        equiltri 
    field
        p1 p2 p3 : Point
    
    side1 : Segment
    side1 = record { point1 = p2 ; point2 = p3 }

    side1' = seg-inverse side1

    side2 : Segment
    side2 = record { point1 = p3 ; point2 = p1 }

    side2' = seg-inverse side2

    side3 : Segment
    side3 = record { point1 = p1 ; point2 = p2 } 

    side3' = seg-inverse side3

    field
        side12 : Segment= side1 side2
        side23 : Segment= side2 side3
        side31 : Segment= side3 side1

    side21' = seg-eq (segment p3 p1) (segment p3 p2)

-- Euclid's Postulate 3
record Circle : Set where
    constructor
        circle
    field 
        center redge : Point 
    
    radius : Segment
    radius = segment center redge

postulate
    circle-intersection : (c1 c2 : Circle) → Point

postulate
    -- Euclid Postulate 1 / Hilbert Inclidence 1
    drawLine : (A B : Point) → Line
    drawSeg : (A B : Point) → Segment
    -- Postulate 2
    extendsSeg : (ab : Line) (AB : Segment) (C : Point) → Line-Contains-Segment AB ab → Line-Contains-Point C ab → Segment


if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

--isRightAngle : Angle → Bool
--isRightAngle a = if (Angle.degree a == 90) then true else false

_and_ : Bool → Bool → Bool
_and_ true true = true 
_and_ false _ = false 
_and_ _ false = false 

postulate
    intersection : Circle → Segment → Point -- Intersection of a line and a Circle1



-- Proposition 1: forming an equilateral triangle from a single segment
prop-1 : (ab : Segment) → EquilTri
prop-1 (segment a b) =
    let 
        c1 : Circle
        c1 = circle a b

        c2 : Circle
        c2 = circle b a

        c : Point 
        c = circle-intersection c1 c2
    in
        equiltri a b c (seg-eq (segment b c) (segment c a)) (seg-eq (segment c a) (segment a b)) (seg-eq (segment a  b) (segment b c)) 
  

-- application of Proposition 1: From a segment, identify a third point that would form an equilateral triangle
create-equilPoint : (ab : Segment) → Point
create-equilPoint (segment a b) =
    let 
        c1 : Circle
        c1 = circle a b

        c2 : Circle
        c2 = circle b a

        c : Point 
        c = circle-intersection c1 c2

        abc : EquilTri
        abc = equiltri a b c (seg-eq (segment b c) (segment c a)) (seg-eq (segment c a) (segment a b)) (seg-eq (segment a  b) (segment b c)) 
  
    in  
        EquilTri.p3 abc

create-equiTri : (ab : Segment) → Point → EquilTri 
create-equiTri (segment A B) C = equiltri A B C (seg-eq (segment B C) (segment C A)) ((seg-eq (segment C A) (segment A B))) ((seg-eq (segment A B) (segment B C)))


-- Helper for proposition 2
postulate
    segment-minus : Segment → Segment → Segment
    segment-minus= : (DL DG DA DB AL BG : Segment) → Segment= DL DG → Segment= DA DB → Segment= AL BG

-- Proposition 2
prop-2 : (A : Point) → (BC : Segment)  → Σ Point (λ L → Segment= (segment A L) BC)
prop-2 a (segment b c) = 
    let 
        abd : EquilTri
        abd = create-equiTri (segment a b) (create-equilPoint (segment a b)) 

        bc : Circle
        bc = circle b c 
            
        dg : Circle
        dg = circle (EquilTri.p3 abd) (intersection bc (segment (EquilTri.p3 abd) b)) 

        l : Point
        l = intersection dg (segment (EquilTri.p3 abd) a) 
            
    in  
        l , seg-trans 
            (segment a l) (segment b (Circle.redge dg)) (segment b c) 
            (segment-minus= 
            (segment (EquilTri.p3 abd) l) (segment (EquilTri.p3 abd) (Circle.redge dg)) 
            (segment (EquilTri.p3 abd) a) (segment (EquilTri.p3 abd) b) 
            (segment a l) (segment b (Circle.redge dg)) 
            (seg-eq (segment (EquilTri.p3 abd) l) (Circle.radius dg)) --both DL and DG are radii of the circle dg 
            ((EquilTri.side21' abd ))) 
            (seg-eq (segment b (Circle.redge dg)) (segment b c)) --both BG and BC are radii of the circle bc 


-- Proposition 4
sas-base : (t1 t2 : Triangle) → Segment= (Triangle.side1 t1) (Triangle.side1 t2) → Segment= (Triangle.side2 t1) (Triangle.side2 t2) 
    → Angle= (Triangle.angle3 t1) (Triangle.angle3 t2) → Segment= (Triangle.side3 t1) (Triangle.side3 t2) 
sas-base a b s1 s2 a3  = seg-eq (segment (Triangle.p1 a) (Triangle.p2 a)) (segment (Triangle.p1 b) (Triangle.p2 b)) 

postulate 
    -- Hilbert Congruence 6, part of proposition 2
    sas-angle2 : (t1 t2 : Triangle) → Seg= (Triangle.side1 t1) (Triangle.side1 t2) → Seg= (Triangle.side2 t1) (Triangle.side2 t2) 
        → Ang= (Triangle.angle3 t1) (Triangle.angle3 t2) → Ang= (Triangle.angle2 t1) (Triangle.angle2 t2)
        
    sas-angle3 : (t1 t2 : Triangle) → Seg= (Triangle.side1 t1) (Triangle.side1 t2) → Seg= (Triangle.side2 t1) (Triangle.side2 t2) 
        → Ang= (Triangle.angle3 t1) (Triangle.angle3 t2) → Ang= (Triangle.angle3 t1) (Triangle.angle3 t2)

-- Proposition 6 : If in a triangle two angles equal one another, then the sides opposite the equal angles also equal one another.
prop6_ang12 : (t1 : Triangle) → Ang= (Triangle.angle1 t1) (Triangle.angle2 t1) → Seg= (Triangle.side1 t1) (Triangle.side2 t1)
prop6_ang12 record { p1 = point1 ; p2 = point2 ; p3 = point3 } ang= = seg=  

prop6_ang23 : (t1 : Triangle) → Ang= (Triangle.angle2 t1) (Triangle.angle3 t1) → Seg= (Triangle.side2 t1) (Triangle.side3 t1)
prop6_ang23 record { p1 = point1 ; p2 = point2 ; p3 = point3 } ang= = seg= 

prop6_ang31 : (t1 : Triangle) → Ang= (Triangle.angle3 t1) (Triangle.angle1 t1) → Seg= (Triangle.side3 t1) (Triangle.side1 t1)
prop6_ang31 record { p1 = point1 ; p2 = point2 ; p3 = point3 } ang= = seg=    

postulate
    _<a_ : Angle → Angle → Set 
    _<s_ : Segment → Segment → Set
    ang-comp : (A B : Angle) → _<a_ A B
postulate
    prop19-12 : (ABC : Triangle) → _<a_ (Triangle.angle1 ABC) (Triangle.angle2 ABC) → _<s_ (Triangle.side1 ABC) (Triangle.side2 ABC) 
    prop19-21 : (ABC : Triangle) → _<a_ (Triangle.angle2 ABC) (Triangle.angle1 ABC) → _<s_ (Triangle.side2 ABC) (Triangle.side1 ABC) 
    prop19-23 : (ABC : Triangle) → _<a_ (Triangle.angle2 ABC) (Triangle.angle3 ABC) → _<s_ (Triangle.side2 ABC) (Triangle.side3 ABC) 
    prop19-32 : (ABC : Triangle) → _<a_ (Triangle.angle3 ABC) (Triangle.angle2 ABC) → _<s_ (Triangle.side3 ABC) (Triangle.side2 ABC) 
    prop19-31 : (ABC : Triangle) → _<a_ (Triangle.angle3 ABC) (Triangle.angle1 ABC) → _<s_ (Triangle.side3 ABC) (Triangle.side1 ABC) 
    prop19-13 : (ABC : Triangle) → _<a_ (Triangle.angle1 ABC) (Triangle.angle3 ABC) → _<s_ (Triangle.side1 ABC) (Triangle.side3 ABC) 
    