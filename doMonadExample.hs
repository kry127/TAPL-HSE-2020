makeList :: [Int]
makeList = do
  x <- [1..3]
  y <- [65,62..27]
  let z = x + y
  return z