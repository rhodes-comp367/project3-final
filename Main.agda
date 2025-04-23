module Main where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool


postulate
    Point : Set 
    Line : Set
    Contains : Point → Line → Set
    drawLine : (A B : Point) → Line

record Angle : Set where
    constructor
        angle 
    field
        line1 : Line
        line2 : Line
        degree : Nat
    
record Triangle : Set where
    constructor
        triangle 
    field 
        line1 : Line
        line2 : Line
        ang : Angle 
    
postulate
    Distance : Nat → Set 

record Circle (n : Nat) : Set where
    constructor
        circle
    field 
        center : Point
        radius : Distance n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

isRightAngle : Angle → Bool
isRightAngle a = if (Angle.degree a == 90) then true else false



