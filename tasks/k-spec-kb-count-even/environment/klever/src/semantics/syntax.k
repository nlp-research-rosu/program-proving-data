// reference/src/semantics/syntax.k — MPY-SYNTAX

module MPY-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  imports BOOL-SYNTAX
  imports STRING-SYNTAX

  syntax Expr ::= "Int"      "(" Int ")"
                | "Float"    "(" Float ")"
                | "Bool"     "(" Bool ")"
                | "Name"     "(" String ")"
                | "Str"      "(" String ")"
                | "UnaryOp"  "(" String "," Expr ")" [strict(2)]
                | "BinOp"    "(" String "," Expr "," Expr ")" [seqstrict(2, 3)]
                | "BoolOp"    "(" String "," Exprs ")"
                | "ListExpr"  "(" Exprs ")"
                | "DictExpr"  "(" Entries ")"
                | "ListComp"  "(" Expr "," CompFors ")" [macro]
                | "GenExp"    "(" Expr "," CompFors ")" [macro]
                | "TupleExpr" "(" Exprs ")"
                | "Subscript" "(" Expr "," Index ")"
                | "IfExp"     "(" Expr "," Expr "," Expr ")" [strict(1)]
                | "Lambda"    "(" Params "," Expr ")"
                | "KwArg"     "(" String "," Expr ")"
                | "Lambda"    "(" Params "," CellVars "," FreeVars "," Expr ")"
                | "NoneVal"
                | "Call"      "(" Expr "," Exprs ")"
                | "Attribute" "(" Expr "," String ")" [strict(1)]
                | "Compare"   "(" Expr "," CmpOp ")"

  syntax CmpOp    ::= "CmpOp" "(" String "," Expr ")"
  syntax Entry    ::= "Entry" "(" Expr "," Expr ")"
  syntax Entries  ::= List{Entry, ","}
  syntax CompFor  ::= "CompFor" "(" Expr "," Expr "," Exprs ")"
  syntax CompFors ::= List{CompFor, ""}
  syntax Exprs    ::= List{Expr, ","}
  syntax Index    ::= Expr | "Slice" "(" Bound "," Bound "," Bound ")"
  syntax Bound    ::= Expr | "NoBound"

  syntax Stmt ::= "Assign"    "(" Expr "," Expr ")" [strict(2)]
                | "Import"    "(" String ")"
                | "ImportFrom" "(" String "," ParamNames ")"
                | "AugAssign" "(" Expr "," String "," Expr ")" [strict(3)]
                | "For"       "(" Expr "," Expr "," Stmts ")" [strict(2)]
                | "While"     "(" Expr "," Stmts ")"
                | "Break"
                | "Continue"
                | "If"        "(" Expr "," Stmts "," Stmts ")" [strict(1)]
                | "Return"    "(" Expr ")" [strict]
                | "Assert"    "(" Expr ")" [strict]
                | "Expr"      "(" Expr ")" [strict]
                | "FuncDef"   "(" String "," Params "," Stmts ")"
                | "FuncDef"   "(" String "," Params "," CellVars "," FreeVars "," Stmts ")"

  syntax Stmts      ::= List{Stmt, ""}
  syntax Params     ::= "Params" "(" ParamNames ")"
  syntax CellVars   ::= "CellVars" "(" ParamNames ")"
  syntax FreeVars   ::= "FreeVars" "(" ParamNames ")"
  syntax ParamNames ::= List{String, ","}
  syntax Module     ::= "Module" "(" Stmts ")"
endmodule
