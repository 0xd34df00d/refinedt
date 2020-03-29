## Good examples

What'd be nice to decide automatically?
```haskell
Value : Type
Value = { ν : Int | ν >= 0 & ν <= 100 }

Weight : Type
Weight = { ν : Int | ν > 0 }

weightedAvg : [(Weight, Value)] -> Value
weightedAvg [] = 0
weightedAvg wvals = sumVals `div` totalWeight
  where
    sumVals = sum $ fmap (\(w, x) -> w * x) wvals
    totalWeight = sum $ fmap fst wvals
```