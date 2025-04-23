module Main where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

-- Definitions
postulate 
    Point : Set 
    Line : Set
    Contains : Point → Line → Set

record Segment : Set where
    constructor
        segment 
    field
        point1 point2 : Point

postulate
    Segment= : Segment → Segment → Set

record Angle : Set where
    constructor
        angle 
    field
        seg1 : Segment
        seg2 : Segment
        -- degree : Nat
    
record Triangle' : Set where
    constructor
        triangle 
    field 
        line1 : Line
        line2 : Line
        ang : Angle

record Triangle : Set where
    field
        point1 point2 point3 : Point
    
    side1 : Segment
    side1 = record { point1 = point2 ; point2 = point3 }

    side2 : Segment
    side2 = record { point1 = point3 ; point2 = point1 }

    side3 : Segment
    side3 = record { point1 = point1 ; point2 = point2 }

    angle1 : Angle
    angle1 = angle side2 side3 

    angle2 : Angle
    angle2 = angle side3 side1 
    
    angle3 : Angle
    angle3 = angle side1 side2

postulate
    Angle= : Angle → Angle → Set
     
postulate
    Distance : Nat → Set 

record Circle (n : Nat) : Set where
    constructor
        circle
    field 
        center : Point
        radius : Distance n

-- Euclid 5 postulates
postulate
    -- Postulate 1
    drawLine : (A B : Point) → Line
    

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
    lineEq : Line → Line → Bool
    angleEq : Angle → Angle → Bool

-- Proposition 4
--equalTriangle : Triangle → Triangle → Bool
--equalTriangle (triangle line1 line2 ang) (triangle line3 line4 ang₁) = if ((lineEq line1 line3 and lineEq line2 line4) and angleEq ang ang₁) then true else false 

sas-base : (t1 t2 : Triangle) → Segment= (Triangle.side1 t1) (Triangle.side1 t2) → Segment= (Triangle.side2 t1) (Triangle.side2 t2) 
    → Angle= (Triangle.angle3 t1) (Triangle.angle3 t2) → Segment= (Triangle.side3 t1) (Triangle.side3 t2) 
sas-base a b s1 s2 a3  = {!   !}
