module Main

import Opetope
import OpetopesUtils
import Face
import Contraction

op : String
op = show $ (dim $ Point "aaa")

main : IO ()
main = putStrLn op
