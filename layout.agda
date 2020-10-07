data Program = List Item
data Item = Let String Term | Main Arity Term
data Arity = Num
data Term = Abstract String Term | Apply Term Term | Var String
