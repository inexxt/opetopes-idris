module Main

import Opetope
import OpetopesUtils

op : String
op = show $ (dim $ Point "aaa")

main : IO ()
main = putStrLn op
