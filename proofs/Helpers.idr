module Helpers

import Data.List
import Data.List.Elem

%default total

public export
data Sublist : (sub : List a) -> (ls : List a) -> Type where
  EmptyIsSublist  : Sublist [] ls
  IgnoreHead      : (rest : Sublist sub ls) -> Sublist sub (_ :: ls)
  AppendBoth      : (rest : Sublist sub ls) -> Sublist (x :: sub) (x :: ls)

export
sublistSelf : (ls : List a) -> Sublist ls ls
sublistSelf [] = EmptyIsSublist
sublistSelf (_ :: xs) = AppendBoth $ sublistSelf xs

export
superListHasElems : Sublist sub super -> Elem x sub -> Elem x super
superListHasElems (IgnoreHead rest) elemPrf = There (superListHasElems rest elemPrf)
superListHasElems (AppendBoth _) Here = Here
superListHasElems (AppendBoth rest) (There later) = There (superListHasElems rest later)

export
elemSwap : {xs : _}
        -> Elem e (xs ++ x1 :: x2 :: ys)
        -> Elem e (xs ++ x2 :: x1 :: ys)
elemSwap {xs = []} Here = There Here
elemSwap {xs = []} (There Here) = Here
elemSwap {xs = []} (There (There rest)) = There (There rest)
elemSwap {xs = x :: xs} Here = Here
elemSwap {xs = x :: xs} (There rest) = There (elemSwap rest)
