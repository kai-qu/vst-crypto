max_BYTE :: Int
max_BYTE = 255

max_TWO_POW :: Int
max_TWO_POW = 7

fst' :: (a, b, c) -> a
fst' (a, b, c) = a

-- ignore False
byte_to_bit :: Int -> [(Bool, Int, Int)]
  -- let bitAt (prevBool, pos, num) =
  --   let numSubtracted = num - 2^pos in
  --   if numSubtracted >= 0
  --      then (True, pos - 1, numSubtracted)
  --           else (False, pos - 1, num) in
byte_to_bit n = take 8 $ iterate bitAt (False, max_TWO_POW + 1, n)
  where bitAt (prevBool, pos, num) = 
          if numSubtracted >= 0
          then (True, pos - 1, numSubtracted)
          else (False, pos - 1, num)
          where numSubtracted = num - 2^pos
