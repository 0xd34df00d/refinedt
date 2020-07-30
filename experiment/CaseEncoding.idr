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
  ADTEnc = (α : Type)
        -> (f0 : T0 -> α)
        -> (f1 : T1 -> α)
        -> α

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



namespace BBExt2
  mutual
    ADTExt : Type
    ADTExt = (S : Type)
          -> (P : S -> Type)
          -> (f0 : (x0 : T0) -> P (l0 S x0))
          -> (f1 : (x1 : T1) -> P (l1 S x1))
          -> (s : S)
          -> P s

    l0 : (S : Type) -> T0 -> S
    l1 : (S : Type) -> T1 -> S



namespace BBExt
  postulate ADTExt : Type
  postulate l0 : T0 -> ADTExt
  postulate l1 : T1 -> ADTExt
  postulate dElim : (P : ADTExt -> Type)
                 -> ((x0 : T0) -> P (l0 x0))
                 -> ((x1 : T1) -> P (l1 x1))
                 -> (s : ADTExt)
                 -> P s

  dMatch : (α : Type)
        -> (s : ADTExt)
        -> ((x0 : T0) -> s = l0 x0 -> α)
        -> ((x1 : T1) -> s = l1 x1 -> α)
        -> α
  dMatch α s f0 f1 = dElim P f0 f1 s Refl
    where
      P : ADTExt -> Type
      P x = s = x -> α

  encode : ADT -> ADTExt
  encode (L0 x0) = l0 x0
  encode (L1 x1) = l1 x1

  test : ADT -> Int
  test x = dMatch Int (encode x) (\(MkT0 n), prf => n) (\(MkT1 n), prf => -n)
