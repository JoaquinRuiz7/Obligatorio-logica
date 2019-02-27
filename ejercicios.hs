module Ejercicios where 
import DN_Prop
--Alumno : Joaquin Ruiz 
-- Nro estudiandte : 206164 
p = L "p"
q = L "q"
r = L "r"
s = L "s"
-- Ej 1
-- Los ejercicios los planteo de arriba para abajo despues de hacerlos en papel.
a = intro_Im (p) (hyp p) 
b = intro_Im (q) (hyp p)
-- ejercicio 1 c.
arbolc = e_Im  (hyp (p :> q)) (hyp p)
c = intro_Y (hyp p) (arbolc) 
-- ejercicio 1 d.
arbold = e_neg (hyp p) (hyp (N p))
d = raa q (arbold)
-- ejercicio 1 e.
arbolEder = e_YD (hyp (p :& (N p))) -- eliminacion del y por derecha  (con no p debajo).
arbolEIzq = e_YI (hyp (p :& (N p))) -- eliminacio del y por izquierda  (con p abajo).
arbolEEN = e_neg (arbolEIzq) (arbolEder) -- raa con el arbol a la izquierda y derecha (los arboles de arriba).
e = i_neg (( p :& (N p))) (arbolEEN)
-- ejercicio 1 f.
arbolF = e_Im (hyp ((N q) :> (N p))) (hyp (N q)) -- eliminacion del implicacon N p abajo. 
arbolF2 = e_neg (hyp p ) (arbolF) -- eliminacion de la negacion con p y no p. 
arbolF3 = raa q (arbolF2) -- raa.
f = intro_Im (p) (arbolF3) 
-- Ejercicio 1 g .
arbolG = e_YD (hyp (q :& r)) -- eliminacion y derecha con r (parte derecha del arbol desps de la e V).
arbolG2 = i_OD p arbolG -- intro del V por derecha (en la parte deerecha del arbol desps de la e V).
arbolG3 = i_OD p (hyp r) -- intro del o por derecha (en la parte izquierda del arbol desps de la e V).
g = e_o (arbolG3) (arbolG2) (hyp (p :| (q :& r)))
-- Ejercicio 1 h .
arbolhD = i_OI (  N p ) ( hyp (  p  ) ) -- parte derecha
arbolhD2 = e_neg ( arbolhD ) ( hyp ( N  ( p :| ( N p) ) ) ) -- parte derecha
arbolhD3 = i_neg ( p ) ( arbolhD2 ) -- parte derecha.
-- parte izquierda
arbolhI = i_OD ( p ) ( hyp ( N p ) ) 
arbolhI2 = e_neg ( arbolhI ) ( hyp ( N ( p :| (N p ) ) ) )
arbolhI3 = raa p ( arbolhI2 )
-- partes izquierda y derecha unidas.
arbolhD5 = e_neg ( arbolhI3 )  ( arbolhD3 )
h = raa ( p :| ( N p ) ) arbolhD5
-- Ejercicio 1 i.
arboliD = e_Im ( hyp ( p :> q ) ) ( hyp p ) -- parte derecha 
arboliD2 = i_OD s (arboliD) -- parte derecha.
arboliI = e_Im ( hyp ( r :> s ) ) ( hyp r ) -- parte izquierda.
arboliI2 = i_OI q ( arboliI) -- parte izquierda.
i = e_o ( arboliI2 ) ( arboliD2 ) ( hyp ( r :| p ) )



--Ej 2 
a2 = e_YI ( hyp ( p :| ( q :& r ) ) )
b2 = e_YD (hyp (N ( N p)))
c2 = e_Im ( hyp ( ( N p ) :| q ) ) ( hyp p )
d2 = e_Im ( hyp ( ( p :> B ) :> B ) ) ( hyp p) 
e2 = bot_E q ( hyp p )
f2 = e_neg ( hyp p ) ( hyp ( N q ) )
g2 = e_neg ( hyp ( p :& q )  ) ( hyp ( N ( ( q  :&   p ) ) ) ) 
h2 = raa p ( hyp ( ( N p ) :& ( p ) ) )
-- ej 2 i.
arboli = e_neg ( hyp p ) ( hyp ( N p ) ) -- eliminacion de la negacion con p y no p.
arboli2 = bot_E q ( arboli ) -- eliminacion del botom con q y el arbol de arriba. 
i2 = i_neg ( p ) ( arboli2 ) -- introduccion de la negacion con p .
-- ej 2 f.
arboljIzq = i_OI ( q ) ( hyp ( p :| q ) )
-- ej 2 j .
arboljD = i_OI ( p ) ( hyp ( q ) )
arboljI = i_OD ( q ) ( hyp ( p ) )
j2 = e_o ( arboljI ) ( arboljD ) ( hyp ( p :& q ) )
-- ej 2 k.
arbolKD = i_OD ( p ) ( hyp q ) -- parte derecha
arbolKI = i_OD ( q ) ( hyp p ) -- parte izquierda.
k = e_o ( arbolKI ) ( arbolKD ) ( hyp ( p :| q ) )
