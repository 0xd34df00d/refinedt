module CaseEncoding

%default total

data T0 = MkT0
data T1 = MkT1

data ADT = L0 T0
         | L1 T1

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
