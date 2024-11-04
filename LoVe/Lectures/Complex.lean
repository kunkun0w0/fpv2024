import Mathlib

namespace new

structure Complex : Type where
  real : ℝ
  im   : ℝ

#check Complex.real

def Complex.add (a b : Complex) : Complex where
  real := a.real + b.real
  im   := a.im + b.im

-- (x + iy)*(z + iw) = ((xz - wy) + i(zy + xw) )
def Complex.mul (a b : Complex) : Complex where
  real := a.real * b.real - a.im * b.im
  im   := a.im*b.real + a.real*b.im

def zero : Complex where
  real := 0
  im := 0

lemma zero_add (a : Complex) : Complex.add zero a = a := by
  simp [zero, Complex.add]

def Complex.neg (a : Complex) : Complex where
  real := -a.real
  im := -a.im

instance : CommRing Complex :=
{ add := Complex.add
  mul := Complex.mul
  zero := zero
  neg := Complex.neg
  add_assoc := _
  zero_add := zero_add
  add_zero := _
  add_left_neg := _
  add_comm := _
  left_distrib := _
  --right_distrib', 'zero_mul', 'mul_zero', 'mul_assoc', 'one', 'one_mul', 'mul_one', 'mul_comm'
    }



example (a b : Complex) : a + b = b + a := by ring

-- example (a b : ℕ) : (a : Complex) + b = b + a := by


structure Polar : Type where
  angle : ℝ
  magnitude : ℝ
  -- angle_above : -Real.pi / 2 < angle
  -- angle_below : Real.pi / 2 > angle
  -- magnitude_nonneg : 0 ≤ magnitude

#check Complex.tan
noncomputable def Complex.toPolar (a : Complex) : Polar where
  angle := Real.arctan (a.im / a.real)
  magnitude := Real.sqrt (a.real^2 + a.im^2)
  -- magnitude_nonneg := by exact Real.sqrt_nonneg (a.real ^ 2 + a.im ^ 2)
  -- angle_nonneg := by exact?

noncomputable def Polar.toComplex (p : Polar) : Complex where
  real := p.magnitude * Real.cos p.angle
  im := p.magnitude * Real.sin p.angle

theorem to_and_from (p : Polar) : p.toComplex.toPolar = p := by
  cases' p with angle magnitude
  simp [Complex.toPolar, Polar.toComplex]
  constructor
  { rw [mul_div_mul_left, ← Real.tan_eq_sin_div_cos]
    rw [Real.arctan_tan]

    }

end new
