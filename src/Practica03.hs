module Practica03 where

-- Tipo de dato Prop
data Prop = 
    Var String |
    Cons Bool |
    Not Prop |
    And Prop Prop |
    Or Prop Prop |
    Impl Prop Prop |
    Syss Prop Prop 
    deriving (Eq)

-- Imprimir el tipo de dato Prop
instance Show Prop where
    show (Cons True) = "Verdadero"
    show (Cons False) = "Falso"
    show (Var p) = p
    show (Not p) = "¬" ++ show p 
    show (Or p q) = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
    show (And p q) = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
    show (Impl p q) = "(" ++ show p ++ " → " ++ show q ++ ")"
    show (Syss p q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")"

-- Fórmulas proposicionales (Variables atómicas)
p, q, r, s, t, u :: Prop
p = Var "p"
q = Var "q"
r = Var "r"
s = Var "s"
t = Var "t"
u = Var "u"

-- Sinonimo para los estados
type Estado = [String]

-- === Funciones auxiliares ===

--Genera el conjunto potencia de una lista
conjuntoPotencia :: [a] -> [[a]]
conjuntoPotencia [] = [[]]
conjuntoPotencia (x:xs) = [(x:ys) | ys <- conjuntoPotencia xs] ++ conjuntoPotencia xs

--Elimina duplicados de una lista de strings
elimiminarDuplicados :: [String] -> [String]
elimiminarDuplicados [] = []
elimiminarDuplicados (x:xs)
    | x `elem` xs = elimiminarDuplicados xs    --Se usa "elem" para evitar crear la funcion auxiliar "pertenece"
    | otherwise = x : elimiminarDuplicados xs



-- === Ejercicios ===

-- Ejercicio 1
--Define la función variables :: Prop -> [String] tal que variables f devuelve el
--conjunto formado por todas las variables proposicionales que aparecen en f
variables :: Prop -> [String]
variables (Var x) = [x]
variables (Cons _) = []
variables (Not f) = variables f
variables (And f1 f2) = elimiminarDuplicados (variables f1 ++ variables f2)
variables (Or f1 f2) = elimiminarDuplicados (variables f1 ++ variables f2)
variables (Impl f1 f2) = elimiminarDuplicados (variables f1 ++ variables f2)
variables (Syss f1 f2) = elimiminarDuplicados (variables f1 ++ variables f2)

-- Ejercicio 2
--Define la función interpretacion :: Prop -> Estado -> Bool tal que
--interpretacion f i es la interpretación de la fórmula f bajo i
interpretacion :: Prop -> Estado -> Bool
interpretacion (Cons b) _ = b
interpretacion (Var x) estado = x `elem` estado
interpretacion (Not f) estado = not (interpretacion f estado)
interpretacion (And f1 f2) estado = interpretacion f1 estado && interpretacion f2 estado
interpretacion (Or f1 f2) estado = interpretacion f1 estado || interpretacion f2 estado
interpretacion (Impl f1 f2) estado = not (interpretacion f1 estado) || interpretacion f2 estado
interpretacion (Syss f1 f2) estado = interpretacion f1 estado == interpretacion f2 estado

-- Ejercicio 3
--Define una función que dada una fórmula proposicional, devuelve todos los estados posibles
--con los que podemos evaluar la fórmula
estadosPosibles :: Prop -> [Estado]
estadosPosibles f = conjuntoPotencia (variables f)

-- Ejercicio 4
--Define una función que dada una fórmula proposicional, esta devuelve la lista de todos
--sus modelos
modelos :: Prop -> [Estado]
modelos f = modelosAux (estadosPosibles f) 
    where
        modelosAux [] = []
        modelosAux (e:es)
            | interpretacion f e = e : modelosAux es
            | otherwise = modelosAux es

-- Ejercicio 5
--Define una función que dadas dos fórmulas φ1 y φ2 de la lógica proposicional, nos diga si
--φ1 y φ2 son equivalentes
sonEquivalentes :: Prop -> Prop -> Bool
sonEquivalentes f1 f2 =
  let todasVars = elimiminarDuplicados (variables f1 ++ variables f2)
      estados = conjuntoPotencia todasVars
  in all(\e -> interpretacion f1 e == interpretacion f2 e) estados

-- Ejercicio 6
--Define una función que dada una fórmula proposicional, nos diga si es una tautología.
tautologia :: Prop -> Bool
tautologia f = all(\e -> interpretacion f e) (estadosPosibles f)

-- Ejercicio 7
-- Definir una función que reciba una lista de fórmulas de la lógica proposicional y una
-- fórmula. Esta función debe determinar si la fórmula recibida es consecuencia lógica de la lista de
-- fórmulas recibida
consecuenciaLogica :: [Prop] -> Prop -> Bool
consecuenciaLogica premisas conclusion =
    let todasVars = obtenerTodasVars premisas
        todosEstados = conjuntoPotencia todasVars
    in verificarConsecuencia todosEstados
    where
        -- Obtiene todas las variables de la lista de premisas y la conclusión
        obtenerTodasVars [] = variables conclusion
        obtenerTodasVars (p:ps) = elimiminarDuplicados (variables p ++ obtenerTodasVars ps)
        
        -- Verifica si todas las premisas son verdaderas en un estado
        todasPremisasVerdaderas _ [] = True
        todasPremisasVerdaderas estado (p:ps) = 
            interpretacion p estado && todasPremisasVerdaderas estado ps
        
        -- Verifica la consecuencia en todos los estados
        verificarConsecuencia [] = True
        verificarConsecuencia (e:es) = 
            (not (todasPremisasVerdaderas e premisas) || interpretacion conclusion e) 
            && verificarConsecuencia es