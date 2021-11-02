import Data.Time

f x = do
    y <- if x == 10 then Just 11 else Nothing; return $ y + 1

g x = [x, x+1]

h x = do
    y <- g x
    z <- g y
    return (x,y,z)

data Prob a = Outcome [(Double, a)]
    deriving (Show)

instance Functor Prob where
    fmap f (Outcome xs) = Outcome [(p, f x) | (p, x) <- xs]

instance Applicative Prob where
    pure x = Outcome [(1.0, x)]
    (Outcome fs) <*> (Outcome xs) = Outcome [(p*p', f x) | (p, f) <- fs, (p', x) <- xs]

instance Monad Prob where
    return x = Outcome [(1.0, x)]
    (Outcome xs) >>= (f) = Outcome [ (p*p', y) | (p, x) <- xs, let Outcome ys = f x, (p', y) <- ys]

simplify [] = []
simplify ((p,x):xs) = (sum (p:map fst (filter ((==x).snd) xs)),x):filter ((/=x).snd) xs

uniform xs = Outcome [(1.0 / fromIntegral (length xs), x) | x <- xs]

dice = uniform [1..6]

toss = uniform [0,1]

factorial n = product [1..n]

binomial n k = product [k+1..n] `div` product [1..n-k]

binomialDist n p = Outcome [(fromIntegral (binomial n k) * (p ^ k) * ((1-p) ^ (n-k)), k) | k <- [0..n]]

displace dist n = fmap (+n) dist

centeredBinomial n = displace (binomialDist n 0.5) (-n `div` 2)

tossTwice = do
    x <- toss;
    y <- toss;
    return (x+y)

diceTwice dice = do
    x <- dice;
    y <- dice;
    return (x+y)

probOf (Outcome xs) f = sum [p | (p, x) <- xs, f x]

main = do
    print (diceTwice dice)
    print [(i, probOf (diceTwice dice) (>=i)) | i <- [2..12]]
    sum <- diceTwice readLn
    print sum
    print [(i, probOf tossTwice (>=i)) | i <- [0..2]]
    print (binomialDist 40 0.5)