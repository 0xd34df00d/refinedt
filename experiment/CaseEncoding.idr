module CaseEncoding

%default total

data T0 = MkT0 Int
data T1 = MkT1 Int

data ADT = L0 T0
         | L1 T1

ex1 : ADT
ex1 = L0 $ MkT0 10

ex2 : ADT
ex2 = L1 $ MkT1 42

namespace BB
  ADTEnc : Type
  ADTEnc = (α : Type) -> (f0 : T0 -> α) -> (f1 : T1 -> α) -> α

  l0 : T0 -> ADTEnc
  l0 n = \α, f0, f1 => f0 n

  l1 : T1 -> ADTEnc
  l1 d = \α, f0, f1 => f1 d


  encode : ADT -> ADTEnc
  encode (L0 x0) = l0 x0
  encode (L1 x1) = l1 x1

  decode : ADTEnc -> ADT
  decode x = x ADT (\x => L0 x) (\x => L1 x)

  correct : (adt : ADT) -> decode (encode adt) = adt
  correct (L0 _) = Refl
  correct (L1 _) = Refl

  test : ADT -> Int
  test x = encode x Int (\(MkT0 n) => n) (\(MkT1 n) => -n)
