structure ArithVar : Type :=
  mk :: (index: Nat)
deriving Repr

inductive ArithBinOp : Type
| add
| sub
| mul

inductive ArithExpr : Type
| lit_expr (from_ : Nat) : ArithExpr
| var_expr (from_var : ArithVar)
| un_op_expr (op: ArithUnOp) (e : ArithExpr)
| bin_op_expr (op : ArithBinOp) (e1 e2 : ArithExpr)

def v₀ := ArithVar.mk 0
def v₁ := ArithVar.mk 1
def v₂ := ArithVar.mk 2

def X := ArithExpr.var_expr v₀
def Y := ArithExpr.var_expr v₁
def Z := ArithExpr.var_expr v₂

#check ArithExpr.bin_op_expr ArithBinOp.add X Y





-- Concrete Syntax
notation " {" v " } " => ArithExpr.var_expr v
notation " { " n " } " => ArithExpr.lit_expr n
notation:max "++" n => ArithExpr.un_op_expr ArithUnOp.inc n
notation:max "--" n => ArithExpr.un_op_expr ArithUnOp.dec n
notation e1 "+" e2 => ArithExpr.bin_op_expr ArithBinOp.add e1 e2
notation e1 "-" e2 => ArithExpr.bin_op_expr ArithBinOp.sub e1 e2
notation e1 "*" e2 => ArithExpr.bin_op_expr ArithBinOp.mul e1 e2


def N := { ( 3 ) }
def M := { ( 4 ) }
def P := { ( 5 ) }

#check X + Y
