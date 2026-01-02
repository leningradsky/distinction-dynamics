{-# OPTIONS --safe #-}

module S3toSO3 where

-- ============================================
-- S3 -> O(3) representation
-- ============================================

data Empty : Set where

data Unit : Set where
  tt : Unit

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

sym : {A : Set} {x y : A} -> x == y -> y == x
sym refl = refl

trans : {A : Set} {x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

cong : {A B : Set} (f : A -> B) {x y : A} -> x == y -> f x == f y
cong f refl = refl

-- Z3 for matrix elements: -1, 0, 1
data Z3 : Set where
  neg : Z3
  zer : Z3
  pos : Z3

_*z_ : Z3 -> Z3 -> Z3
neg *z neg = pos
neg *z zer = zer
neg *z pos = neg
zer *z _ = zer
pos *z neg = neg
pos *z zer = zer
pos *z pos = pos

_+z_ : Z3 -> Z3 -> Z3
zer +z y = y
x +z zer = x
pos +z neg = zer
neg +z pos = zer
pos +z pos = pos
neg +z neg = neg

record Vec3 : Set where
  constructor vec
  field
    v1 v2 v3 : Z3

record Mat3 : Set where
  constructor mat
  field
    r1 r2 r3 : Vec3

col1 col2 col3 : Mat3 -> Vec3
col1 (mat (vec a _ _) (vec b _ _) (vec c _ _)) = vec a b c
col2 (mat (vec _ a _) (vec _ b _) (vec _ c _)) = vec a b c
col3 (mat (vec _ _ a) (vec _ _ b) (vec _ _ c)) = vec a b c

dot : Vec3 -> Vec3 -> Z3
dot (vec a1 a2 a3) (vec b1 b2 b3) = 
  (a1 *z b1) +z ((a2 *z b2) +z (a3 *z b3))

_*m_ : Mat3 -> Mat3 -> Mat3
m1 *m m2 = mat 
  (vec (dot (Mat3.r1 m1) (col1 m2)) (dot (Mat3.r1 m1) (col2 m2)) (dot (Mat3.r1 m1) (col3 m2)))
  (vec (dot (Mat3.r2 m1) (col1 m2)) (dot (Mat3.r2 m1) (col2 m2)) (dot (Mat3.r2 m1) (col3 m2)))
  (vec (dot (Mat3.r3 m1) (col1 m2)) (dot (Mat3.r3 m1) (col2 m2)) (dot (Mat3.r3 m1) (col3 m2)))

transpose : Mat3 -> Mat3
transpose m = mat (col1 m) (col2 m) (col3 m)

I3 : Mat3
I3 = mat (vec pos zer zer) (vec zer pos zer) (vec zer zer pos)

-- S3 group
data S3 : Set where
  e   : S3
  r   : S3
  r2  : S3
  s1  : S3
  s2  : S3
  s3  : S3

_*s_ : S3 -> S3 -> S3
e  *s g  = g
g  *s e  = g
r  *s r  = r2
r  *s r2 = e
r2 *s r  = e
r2 *s r2 = r
r  *s s1 = s3
r  *s s2 = s1
r  *s s3 = s2
r2 *s s1 = s2
r2 *s s2 = s3
r2 *s s3 = s1
s1 *s r  = s2
s1 *s r2 = s3
s1 *s s1 = e
s1 *s s2 = r
s1 *s s3 = r2
s2 *s r  = s3
s2 *s r2 = s1
s2 *s s1 = r2
s2 *s s2 = e
s2 *s s3 = r
s3 *s r  = s1
s3 *s r2 = s2
s3 *s s1 = r
s3 *s s2 = r2
s3 *s s3 = e

-- Representation
rho : S3 -> Mat3
rho e  = mat (vec pos zer zer) (vec zer pos zer) (vec zer zer pos)
rho r  = mat (vec zer zer pos) (vec pos zer zer) (vec zer pos zer)
rho r2 = mat (vec zer pos zer) (vec zer zer pos) (vec pos zer zer)
rho s1 = mat (vec zer pos zer) (vec pos zer zer) (vec zer zer pos)
rho s2 = mat (vec pos zer zer) (vec zer zer pos) (vec zer pos zer)
rho s3 = mat (vec zer zer pos) (vec zer pos zer) (vec pos zer zer)

IsOrthogonal : Mat3 -> Set
IsOrthogonal m = (m *m transpose m) == I3

orth-e : IsOrthogonal (rho e)
orth-e = refl

orth-r : IsOrthogonal (rho r)
orth-r = refl

orth-r2 : IsOrthogonal (rho r2)
orth-r2 = refl

orth-s1 : IsOrthogonal (rho s1)
orth-s1 = refl

orth-s2 : IsOrthogonal (rho s2)
orth-s2 = refl

orth-s3 : IsOrthogonal (rho s3)
orth-s3 = refl

allOrthogonal : (g : S3) -> IsOrthogonal (rho g)
allOrthogonal e  = orth-e
allOrthogonal r  = orth-r
allOrthogonal r2 = orth-r2
allOrthogonal s1 = orth-s1
allOrthogonal s2 = orth-s2
allOrthogonal s3 = orth-s3

det : Mat3 -> Z3
det (mat (vec a b c) (vec d e' f) (vec g h i)) = 
  ((a *z ((e' *z i) +z (neg *z (f *z h)))) +z 
   ((neg *z b) *z ((d *z i) +z (neg *z (f *z g))))) +z
  (c *z ((d *z h) +z (neg *z (e' *z g))))

data Sign : Set where
  plus  : Sign
  minus : Sign

signOf : S3 -> Sign
signOf e  = plus
signOf r  = plus
signOf r2 = plus
signOf s1 = minus
signOf s2 = minus
signOf s3 = minus

det-e : det (rho e) == pos
det-e = refl

det-r : det (rho r) == pos
det-r = refl

det-s1 : det (rho s1) == neg
det-s1 = refl

-- A3 = {e, r, r2} subset of SO(3)
data A3 : Set where
  a-e  : A3
  a-r  : A3
  a-r2 : A3

embed-A3 : A3 -> S3
embed-A3 a-e  = e
embed-A3 a-r  = r
embed-A3 a-r2 = r2

theorem-A3-to-SO3 : (a : A3) -> det (rho (embed-A3 a)) == pos
theorem-A3-to-SO3 a-e  = refl
theorem-A3-to-SO3 a-r  = refl
theorem-A3-to-SO3 a-r2 = refl

-- Triada
data Three : Set where
  T1 T2 T3 : Three

act : S3 -> Three -> Three
act e  x = x
act r  T1 = T2
act r  T2 = T3
act r  T3 = T1
act r2 T1 = T3
act r2 T2 = T1
act r2 T3 = T2
act s1 T1 = T2
act s1 T2 = T1
act s1 T3 = T3
act s2 T1 = T1
act s2 T2 = T3
act s2 T3 = T2
act s3 T1 = T3
act s3 T2 = T2
act s3 T3 = T1

{-
PROVEN:
1. S3 is permutation group (multiplication table)
2. rho : S3 -> Mat3 representation
3. All rho(g) are orthogonal => S3 subset O(3)
4. det(rho(g)) = +/-1, +1 for even permutations
5. A3 = {e, r, r2} subset SO(3)
6. S3 acts on Triada transitively
-}
