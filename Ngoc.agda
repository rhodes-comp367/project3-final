module Ngoc where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl ; sym ; trans)


-- Definitions
postulate 
    Point : Set 
    Line : Set
    Contains : Point → Line → Set
    Congruence : Line → Line → Set
    EquilateralTriangle : (A B : Point) → Point
    


data Point= : Point → Point → Set where
  point= : ∀ {p} → Point= p p

point-refl : (p : Point) → Point= p p
point-refl _ = point=

record Segment : Set where
    constructor
        segment 
    field
        point1 point2 : Point

postulate
    Segment= : Segment → Segment → Set
    seg-eq : (s1 s2 : Segment) → Segment= s1 s2  

data Seg= : Segment → Segment → Set where
  seg= : ∀ {s1 s2} → Seg= s1 s2


postulate
    Distance : Nat → Set 

record Angle : Set where
    constructor
        angle 
    field
        seg1 : Segment
        seg2 : Segment
        -- degree : Nat

postulate
    Angle= : Angle → Angle → Set
    ang-eq : (a1 a2 : Angle) → Angle= a1 a2  
    
data Ang= : Angle → Angle → Set where
  ang= : ∀ {a1 a2} → Ang= a1 a2

record Triangle' : Set where
    constructor
        triangle 
    field 
        line1 : Line
        line2 : Line
        ang : Angle

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

    side2 : Segment
    side2 = record { point1 = p3 ; point2 = p1 }

    side3 : Segment
    side3 = record { point1 = p1 ; point2 = p2 }

    side1' : Segment
    side1' = record {point1 = p3; point2 = p1}

    side2' : Segment
    side2' = record {point1 = p1; point2 = p3}

    side32' : Segment= side3 side2'
    side32' = seg-eq (segment p1 p2) (segment p1 p3) 

    field
        side12 : Segment= side1 side2
        side23 : Segment= side2 side3
        side31 : Segment= side3 side1

    side21' = seg-eq (segment p3 p1) (segment p3 p2)

record Circle : Set where
    constructor
        circle
    field 
        center edge redge : Point

    radius : Segment
    radius = segment center redge

    radius= : Segment= (segment center edge) (segment center redge) 
    radius= = seg-eq (segment center edge) (segment center redge) 


drawCircle : (center : Point) (edge : Point) (random : Point) → Circle
drawCircle c e r = circle c e r  

postulate
    intersection : Circle → Segment → Point -- Intersection of a line and a circle

-- Axioms
postulate
    -- Euclid Postulate 1 / Hilbert Inclidence 1
    drawLine : (A B : Point) → Line
    -- Postulate 3


if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

--isRightAngle : Angle → Bool
--isRightAngle a = if (Angle.degree a == 90) then true else false

_and_ : Bool → Bool → Bool
_and_ true true = true 
_and_ false _ = false 
_and_ _ false = false 

 
-- Proposition 1
Prop-1 : (ab : Segment) → (c1 c2 : Circle) 
    → Point= (Circle.center c1) (Segment.point1 ab) → Point= (Circle.center c2) (Segment.point2 ab) 
    → Point= (Circle.redge c1) (Circle.center c2) → Point= (Circle.center c1) (Circle.redge c2) 
    → Point= (Circle.edge c1) (Circle.edge c2) → EquilTri
Prop-1 (segment a b) (circle .a edge .b) (circle .b .edge .a) point= point= point= point= point= 
    = equiltri a b edge (seg-eq (segment b edge) (segment edge a)) (seg-eq (segment edge a) (segment a b)) (seg-eq (segment a  b) (segment b edge)) 

create-equiTri : (ab : Segment) → Point → EquilTri 
create-equiTri (segment A B) C = equiltri A B C (seg-eq (segment B C) (segment C A)) ((seg-eq (segment C A) (segment A B))) ((seg-eq (segment A B) (segment B C)))

-- Start proving proposition 2: 
seg-trans : (a b c : Segment) → Segment= a b → Segment= b c → Segment= a c
seg-trans a b c ab bc  = seg-eq a c 

seg-sym : (a b : Segment) → Segment= a b → Segment= b a 
seg-sym a b ab = seg-eq b a

--dab : (A : Point) (BC : Segment) → (DAB : EquilTri) → (circleb circled : Circle) 
--    → Point= (EquilTri.p1 DAB) (Circle.center circled) 
--    → Point= (EquilTri.p2 DAB) A
--    → Point= (EquilTri.p3 DAB) (Circle.center circleb) 
--    → Segment= (segment A (Circle.egde circled)) (segment (Segment.point1 BC) (Circle.redge circleb))
--dab = {!   !} 
postulate
  segment-minus : Segment → Segment → Segment
  segment-minus= : (DL DG DA DB AL BG : Segment) → Segment= DL DG → Segment= DA DB → Segment= AL BG 

subtract-equal : (DAB : EquilTri) → (DL DG : Segment) 
  → Segment= DL DG
  → Point= (Segment.point1 DL) (EquilTri.p1 DAB) → Point= (Segment.point1 DG) (EquilTri.p1 DAB)
  → Segment= (segment-minus DL (EquilTri.side3 DAB)) (segment-minus DG (EquilTri.side2 DAB))
 
subtract-equal (equiltri d a b side12 side23 side31) (segment .d l) (segment .d g) dl=dg point= point= = 
    seg-trans 
        (segment-minus (segment d l) (segment d a)) 
        (segment-minus (segment d g) (segment d a)) 
        (segment-minus (segment d g) (segment b d)) 
        (seg-eq (segment-minus (segment d l) (segment d a))((segment-minus (segment d g) (segment d a)))) 
        (seg-eq ((segment-minus (segment d g) (segment d a))) ((segment-minus (segment d g) (segment b d))))
    where 
        da=db : Segment= (segment b d) (segment d a) 
        da=db = EquilTri.side23 (equiltri d a b side12 side23 side31) 

postulate 
    extend : (p1 p2 : Point) → Segment    

-- Proposition 2
SegSet : (a : Point) → (bc : Segment) → (ab : Segment) → (d : Point) → (abd : EquilTri) → (Cb Cd : Circle) → (al dl bg : Segment) 
    → Point= a (Segment.point1 ab) → Point= (Segment.point1 bc) (Segment.point2 ab) → Point= a (EquilTri.p1 abd) → Point= (Segment.point1 bc) (EquilTri.p2 abd)  → Point= d (EquilTri.p3 abd)
    → Point= a (Segment.point1 al) → Point= d (Segment.point1 dl) → Point= (Segment.point2 al) (Segment.point2 dl) → Point= (Segment.point1 bc) (Segment.point1 bg)
    → Point= (Segment.point1 bc) (Circle.center Cb) → Point= (Segment.point2 bc) (Circle.redge Cb) → Point= (Segment.point2 bg) (Circle.edge Cb) -- → Segment= bc (Circle.radius Cb) 
    → Point= d (Circle.center Cd) → Point= (Segment.point2 dl) (Circle.redge Cd) → Point= (Segment.point2 bg) (Circle.edge Cd) -- → Segment= dl (Circle.radius Cb)
    → Segment= al bg 
SegSet A (segment B C) (segment A B) D (equiltri A B D side12 side23 side31) 
    (circle B G C) (circle D G L) (segment A L) (segment D L) (segment B G) 
    point= point= point= point= point= point= point= point= point= point= point= point= point= point= point= = seg-eq ((segment A L)) ((segment B G))

-- Another proof 
prop2 : (A : Point) (BC : Segment) → (AB : Segment) → (D : Point) → (AD : Segment) → (circleB circleD : Circle)
    → Point= A (Segment.point1 AB) → Point= (Segment.point1 BC) (Segment.point2 AB)
    → Point= A (Segment.point1 AD) → Point= D (Segment.point2 AD)
    → Point= (Segment.point2 BC) (Circle.edge circleB) 
    → Point= (Segment.point1 BC) (Circle.center circleB) 
    → Point= D (Circle.center circleD)
    → Point= D (Circle.edge circleD)
    → Segment= (segment A (Circle.edge circleD)) BC 
prop2 a (segment b c) (segment a b) d (segment a d) (circle .b .c h) (circle d l g)
    point= point= point= point= point= point= point= point= =
    seg-trans (segment a l) (segment b g) (segment b c)
        (segment-minus=
        (segment d l) (segment d g)
        (segment d a) (segment d b)
        (segment a l) (segment b g)
        (Circle.radius= (circle d l g))
        (seg-eq (segment d a) (segment d b)))
        (Circle.radius= (circle b g c)) 
    where
        abd : EquilTri  
        abd = create-equiTri (segment a b) d 

-- proposition 2 with improved type - 1
prop-2 :  {L G D : Point} (A : Point) → (BC : Segment) → Segment= (segment A L) BC
prop-2 {l} {g} {d} a bc = 
    let 
        bgc : Circle
        bgc = circle (Segment.point1 bc) g (Segment.point2 bc)  
            
        abd : EquilTri
        abd = create-equiTri (segment a (Segment.point1 bc)) d

        dlg : Circle
        dlg = circle (EquilTri.p3 abd) l g 
            
    in  
        seg-trans 
            (segment a (Circle.edge dlg)) (segment (Segment.point1 bc) (Circle.edge bgc)) bc 
            (segment-minus= 
                (segment (EquilTri.p3 abd) l) (segment (EquilTri.p3 abd) g) 
                (segment (EquilTri.p3 abd) a) (segment (EquilTri.p3 abd) (Segment.point1 bc)) 
                (segment a (Circle.edge dlg)) (segment (Segment.point1 bc) g) 
                (Circle.radius= dlg) (EquilTri.side21' abd )) 
            (Circle.radius= bgc) 


-- Proposition 4
sas-base : (t1 t2 : Triangle) → Segment= (Triangle.side1 t1) (Triangle.side1 t2) → Segment= (Triangle.side2 t1) (Triangle.side2 t2) 
    → Angle= (Triangle.angle3 t1) (Triangle.angle3 t2) → Segment= (Triangle.side3 t1) (Triangle.side3 t2) 
sas-base a b s1 s2 a3  = seg-eq (segment (Triangle.p1 a) (Triangle.p2 a)) (segment (Triangle.p1 b) (Triangle.p2 b)) 

postulate 
    -- Hilbert Congruence 6
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


    



 