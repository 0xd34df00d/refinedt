module CaseEncoding

%default total

data ADT = L0 Int
         | L1 Double

namespace BB
  ADTEnc : Type
  ADTEnc = (α : Type) -> (f0 : Int -> α) -> (f1 : Double -> α) -> α

  l0 : Int -> ADTEnc
  l0 n = \α, f0, f1 => f0 n

  l1 : Double -> ADTEnc
  l1 d = \α, f0, f1 => f1 d
