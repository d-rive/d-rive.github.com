{-# LANGUAGE MonadComprehensions, DefaultSignatures, DeriveGeneric #-}
--  |>>>
--  |>>>
--  |>>>
--  |
--  |
--  |
--  |
--  |
--  |     The setting is a tutorial on functional algorithm design. There are four
--        students: Anne, Jack, Mary and Theo.

--  |
--  Teacher: Good morning class. Today I would like you design a function
--             invert that takes two arguments: a function f from pairs of natural numbers
--             to natural numbers, and a natural number z. The value invert f z is a list
--             of all pairs (x, y) satisfying f (x, y) = z. You can assume that f is strictly
--             increasing in each argument, but nothing else.

--  |
--  Jack: That seems an easy problem. Since f is a function on naturals and
--          is increasing in each argument, we know that |f (x, y) = z implies x ≤ z and
--          y ≤ z|. Hence we can deﬁne invert by a simple search of all possible pairs of
--          values:

--   ###  |||  invert f z   =  [(x, y) | x ← [0 .. z], y ← [0 .. z], f (x, y)  ==  z]  |||
--  |  ???  Does this solve the problem?

invert    f    z   =    
                    [    (x,y)     |         x  <-  [0  ..  z]
                                   ,         y  <-  [0  ..  z]
                                   ,  f(x,y)      ==        z    ]

--  Example         |  f: \(a,b)        |    z    |    Result                                                           |
--  :-------------  |  :--------------  |  :----: |    -------------------------------------------------------------:
-- >>invert         | \(a,b)  ->  a*b   |   004   |    (1,4)     (2,2)     (4,1)                                        |
-- >>invert         | \(a,b)  ->  a*b   |   024   |    (1,24)  (2,12)  (3,8),  (4,6)  (6,4)  (8,3),  (12,2),  (24,1)    |
-- >>invert         | \(a,b)  ->  a*b   |   019   |    (1,19)  (19,1)                                                   |
-- >>invert         | \(a,b)  ->  a*b   |   123   |    (1,123)   (3,41)    (41,3)    (123,1)                            |
-- >><...>          |                   |         |                                                                     |
--


--   |
--   |  Teacher: Yes it does, but your solution involves   <|O|  (z + 1)^2  |>  evaluations of f .
--   |                  Since f may be very expensive to compute, I would like a solution with as
--   |                  few evaluations of f as possible.

--  |
--   |  Theo: Well, it is easy to halve the evaluations. Since      f (x, y)  ≥         x + y 
--   |                                                         if   f         is        increasing
--   |            the search can be conﬁned to values on or below the diagonal of  the square:  
--   ##  ||  invert f z   =  [(x, y) | x ← [0 .. z], y ← [0 .. z − x], f (x, y)    z]   ||

--   ###  |||
invert'        f    z   =    
                         [  (x,y)  |         x  <-  [0           ..  z  ]
                                   ,         y  <-  [0           ..  z-x  ] --                                 ^
                                   ,  f(x,y)      ==                  z  ]

--   Come to think of it, you can replace the two upper bounds by z − f (0, 0)
--   and z − x − f (0, 0). Then if z < f (0, 0) the search terminates at once.

--		|Anne: Assuming it doesn’t matter in which order the solutions are found,
--		|               I think you can do better still. Jack’s method searches a square of size (z + 1)
--		|               from the origin at the bottom left, and proceeds upwards column by column.
--		|               We can do better if we start at the top-left corner (0, z) of the square. At any
--		|               stage the search space is constrained to be a rectangle with top-left corner
--		|               (u, v) and bottom-right corner (z, 0). 
--		|
--		|Here is the picture:
--   ###  |||

--      --   0,z  .              .   (z,z)
--                o--------------o
--                |    !(u,v)    |    --  !  where  your  binary  search  is  now,  starting  at  z,0
--                |    o---------o
--                |    |         |
--                |    |         |
--                |    |         |
--                o----o---------o    --  !  where  you  start  the  search
--      --   0,0  ^              ^    z,0


--  Let me deﬁne

--   ###  ||  find (u, v) f z   =  [(x, y) | x ← [u .. z], y ← [v, v − 1 .. 0], f (x, y)    z]     ||

--  <...>
--

--  same  results,  but  slightly  faster:
--  diff  [dResult][]    (invert,  invert')  =is=  sometimes  doesn't  return  factors  (1,x)  (x,1)
--  diff  [dt][]  (invert,  invert')  =is=  3096
--        ^^^^^^^^^^^--  none  of  this  shit,  please,  thank  you!

find (u,v)     f    z    =    
                         [  (x,y)  |         x  <-  [u           ..  z]
                                   ,         y  <-  [v,(v-1)     ..  0]
                                   ,  f(x,y) ==  z
                                   ]
                         
invertF        f    z    =
  find'  (0,z) f    z    


find'  (u,v)   f    z    
                         |    u    >    z    &&   v    <    0         =                                            [  ]
                         |              z'   <    z                   =                       find  (u+1,  v)      f  z
                         |              z'   ==   z                   =          (u  ,  v) :  find  (u+1,v-1)      f  z
                         |              z'   >    z                   =                       find  (u  ,v-1)      f  z 
                         where          z'                            =         f(u  ,  v)


-- In the worst case, when ﬁnd traverses the perimeter of the square from the
-- top-left corner to the bottom-right corner, it performs 2z + 1 evaluations
-- of f . 
-- In  the  best  case, when find proceeds directly to either the bottom or
-- rightmost boundary, it requires only z + 1 evaluations.

--  not  much  difference,  a  little  faster  maybe



-- Theo: You can reduce the search space still further because the initial
-- square with top-left corner (0, z) and bottom-right corner (z, 0) is an overly
-- generous estimate of where the required values lie. Suppose we ﬁrst compute
-- m and n, where

--  m   =  maximum (filter (\y -> f (0, y) <= z) [0 .. z])
--  n   =  maximum (filter (\x -> f (x, 0) <= z) [0 .. z])

--  Then we can deﬁne invert f z = ﬁnd (0, m) f z, where ﬁnd has exactly the
--  same form that Anne gave, except that the ﬁrst guard becomes u > n ∨ v < 0.

--  In other words, rather than search a (z+1) × (z+1) square we can get away
--  with searching an (m+1) × (n+1) rectangle.

--  The crucial point is that we can compute m and n by binary search.

--  Let g be an increasing function on the natural numbers and suppose x,
--  y and z satisfy g x ≤ z < g y. i.  To determine the unique value m, where
--  m = bsearch g (x, y)z, in the range x ≤ m < y such that g m ≤ z < g (m +1)
--  we can maintain the invariants g a ≤ z < g b and x ≤ a < b ≤ y. 

--  This leads
--  to the program

bsearch g (a, b) z
                    | a+1 == b     =  a
                    | g m <= z      =  bsearch g (m, b) z
                    |   otherwise  =  bsearch g (a, m) z
          where m = (a + b) `div` 2
--  Since a+1 < b => a < m < y it follows that neither g x nor g y are evaluated
--  by the algorithm, so they can be ﬁctitious values. In particular, we have

findBS    
       (u,v)  (r,s)  f      z
        
               
                      
                             
                                    
     | u > r    ||   v < s         =  []
     | v - s    <=   r - u         =  rfind  (bsearch  (\x  ->  f(x,q))  (u-1,r+1)  z)
     |       otherwise             =  cfind  (bsearch  (\y  ->  f(p,y))  (s-1,v+1)  z)
       where
              p                    = (  u+r)   `div`     2
              q                    = (  v+s)   `div`     2
              rfind  p =    (if  f( p,q)  ==  z  
                             then ( p,q):  findBS  (u,v)  (p-1,q+1)      f  z
                             else          findBS  (u,v)  (p  ,q+1)      f  z
                             )  ++         findBS  (p+1, q-1)  (r,s)     f  z

              cfind  q =    findBS  (u,v)  (p-1,q+1)  f  z
                                   ++ (if  f(p,q)  ==  z  then  (p,q):  findBS  (p+1, q-1)  (r,s)  f  z
                                        else  findBS  (p+1,  q)  (r,s)  f  z
                                        )

i  f  z      =    findBS    (0,m)  (n,0)
                                                            f    
                                                                                z
     where
               m    =    bsearch   (\y  ->  f  (0,y))       (negate  1,  z+1)       
                                                                                z
               n    =    bsearch   (\x  ->  f  (x,0))       (negate  1,  z+1)   z
                                   

--  where we extend f with ﬁctitious values f (0, − 1) = 0 and f ( − 1, 0) = 0.
--  This version of invert takes about 2 log z + m + n evaluations of f in the
--  worst case and 2 log z + m min n in the best case. Since m or n may be
--  substantially less than z, for example when f (x, y) = 2
--  x
--  + 3
--  y
--  , we can end  up with an algorithm that takes only O(log z) steps in the worst case.


