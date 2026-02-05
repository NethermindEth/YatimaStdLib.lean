class YatimaRing (R : Type) extends Add R, Mul R, Sub R, HPow R Nat R, BEq R, Coe Nat R where
  zero : R
  one : R

namespace YatimaRing

instance {R : Type _} [Add R] [Mul R] [Sub R] [OfNat R (nat_lit 0)] [OfNat R (nat_lit 1)]
  [HPow R Nat R] [BEq R] [Coe Nat R] : YatimaRing R where
  zero := 0
  one := 1

instance : YatimaRing Nat where
  zero := 0
  one := 1
  coe := id

instance : YatimaRing Int where
  zero := 0
  one := 1
  coe := fun n => n

instance [YatimaRing R] : OfNat R (nat_lit 0) where
  ofNat := zero

instance [YatimaRing R] : OfNat R (nat_lit 1) where
  ofNat := one

instance [YatimaRing R] : Neg R where
  neg x := 0 - x

instance [YatimaRing R] : Inhabited R where
  default := 0

end YatimaRing

class YatimaField (K : Type) extends YatimaRing K where
  inv : K → K

namespace YatimaField

instance [YatimaField K] : Div K where
  div a b := a * YatimaField.inv b

postfix:max "⁻¹" => inv

end YatimaField
