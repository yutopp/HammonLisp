module HAMMON-LISP-SYNTAX
  syntax Expr ::= SId | Int | "nil" | "t"
                | "(" SList ")"

  syntax SList ::= List{Expr, ""}

  syntax SOp ::= "+" | "-" | "*"
               | "="
  syntax SId ::= Id | SOp
               | "defun"
               | "progn"
               | "lambda"
               | "if"
               | "print"

endmodule

module HAMMON-LISP
  imports HAMMON-LISP-SYNTAX

  syntax KItem ::= "%t" | "%nil"
  syntax KResult ::= Int | SId | "%t" | "%nil"
  syntax KItem ::= "%toplevel"

  configuration <k> %toplevel $PGM:SList </k>
                <venv> .Map </venv>
                <fenv> .Map </fenv>
                <store> .Map </store>
                <nextLoc> 0 </nextLoc>
                <results> .List </results>
                <out stream="stdout"> .List </out>


  // rewrite parentheses to << >>
  // it is needed to avoid confusion of K parsers...
  syntax Expr ::= "<<" SList ">>"
  rule ( E:SList ):Expr => << E >>  [macro]


  // Variables
  rule <k> X:Id => Val ... </k>
       <venv> ... X |-> Loc ... </venv>
       <store> ... Loc |-> Val ... </store>

  // special value
  rule <k> nil => %nil ... </k>
  rule <k> << .SList >> => %nil ... </k>
  rule <k> t => %t ... </k>

  // ===
  // special forms
  // ===

  syntax KItem ::= isSpecialFormOrBuiltin(Expr)     [function, boolOperation]
  rule isSpecialFormOrBuiltin(_:SOp)        => true
  rule isSpecialFormOrBuiltin(defun:SId)    => true
  rule isSpecialFormOrBuiltin(progn:SId)    => true
  rule isSpecialFormOrBuiltin(lambda:SId)   => true
  rule isSpecialFormOrBuiltin(if:SId)       => true
  rule isSpecialFormOrBuiltin(print:SId)    => true
  rule isSpecialFormOrBuiltin(_:Expr)       => false

  // defun
  syntax KItem ::= func(SId, SList, SList, Map, Map, Int)

  syntax KItem ::= midDefunCheckParam(SList)
  rule <k> << defun:SId Sym:SId << Params:SList >>:Expr Exprs:SList >> => midDefunCheckParam(Params) ~> Sym ... </k>
       <venv> VEnv </venv>
       <fenv> FEnv => FEnv[Sym <- N +Int 1] </fenv>
       <store> Sto => Sto[ N +Int 1 <- func(Sym, Params, Exprs, VEnv, FEnv, N +Int 1)] </store>
       <nextLoc> N => N +Int 1 </nextLoc>

  rule midDefunCheckParam(P:Id Ps:SList) => midDefunCheckParam(Ps)      [structural]
  rule midDefunCheckParam(.SList) => .K                                 [structural]


  // lambda
  rule <k> << lambda:SId << Params:SList >>:Expr Exprs:SList >> => midDefunCheckParam(Params) ~> ?Sym ... </k>
       <venv> VEnv </venv>
       <fenv> FEnv => FEnv[?Sym <- N +Int 1] </fenv>
       <store> Sto => Sto[ N +Int 1 <- func(?Sym:Id, Params, Exprs, VEnv, FEnv, N +Int 1)] </store>
       <nextLoc> N => N +Int 1 </nextLoc>


  // progn
  rule <k> << progn:SId TE:Expr (E:Expr Es):SList >> => TE ~> ignoreVal ~> << progn:SId E Es >> ... </k>
       [structural]
  rule <k> << progn:SId TE .SList >> => TE ... </k>
       [structural]


  // if
  syntax KItem ::= midCond(Expr, Expr)
  rule <k> << if:SId Cond:Expr Then:Expr Else:Expr >> => Cond ~> midCond(Then, Else) ... </k>
       [structural]
  rule <k> CV:KResult ~> midCond(Then, Else) => Then ... </k>
       when CV =/=K %nil
       [structural]
  rule <k> %nil ~> midCond(_, Else) => Else ... </k>
       [structural]



  // ===
  // builtin functions
  // ===

  // print
  syntax KItem ::= "printOp"
  rule <k> << print:SId E:Expr >> => E ~> printOp ... </k>
  rule <k> V:KResult ~> printOp => V ... </k>
       <out> ... .List => ListItem(toPrintable(V)) ListItem("\n") </out>

  syntax KItem ::= toPrintable(Expr)    [function]
  rule toPrintable(I:Int)       => I
  rule toPrintable(N:SId)       => N
  rule toPrintable(%t)          => "T"
  rule toPrintable(%nil)        => "Nil"


  /// Operators
  syntax KItem ::= "arithStore" | arithOp(SOp, Expr)
  rule <k> << Op:SOp E:Expr Es:SList >> => E ~> arithStore ~> << Op:SOp Es >> ... </k>
       [structural]
  rule <k> V:KResult ~> arithStore ~> << Op:SOp (E:Expr Es):SList >> =>
             E ~> arithOp(Op, V) ~> arithStore ~> << Op:SOp Es:SList >> ... </k>
       [structural]
  rule <k> V:KResult ~> arithStore ~> << Op:SOp .SList >> => V ... </k>

  // +
  rule <k> V2:Int ~> arithOp(+, V1:Int) => V1 +Int V2 ... </k>

  // -
  rule <k> V2:Int ~> arithOp(-, V1:Int) => V1 -Int V2 ... </k>

  // *
  rule <k> V2:Int ~> arithOp(*, V1:Int) => V1 *Int V2 ... </k>

  // =
  rule <k> V2:Int ~> arithOp(=, V1:Int) => t ... </k>
       when V1 ==Int V2
  rule <k> V2:Int ~> arithOp(=, V1:Int) => nil ... </k>
       when V1 =/=Int V2


  // ===
  // call
  // ===
  syntax KItem ::= midFApply(SList) | midBeginApply(K, SList)
  rule <k> << E:Expr Args:SList >> => E ~> midFApply(Args) ... </k>
       when notBool isSpecialFormOrBuiltin(E)
       [structural]

  rule <k> Sym:Id ~> midFApply(Args) => midBeginApply(Func, Args) ... </k>
       <fenv> ... Sym |-> Loc ... </fenv>
       <store> ... Loc |-> Func ... </store>
       [structural]

  syntax KItem ::= midConv(SList, SList, Map, Map) | midEndApply(Map, Map)
  rule <k> midBeginApply(func(Sym, Params, Body, FVEnv, FFEnv, N), Args) =>
                midConv(Params, Args, FVEnv, FFEnv[Sym <- N])
                ~> << progn Body >>
                ~> midEndApply(VEnv, FEnv) ...
       </k>
       <venv> VEnv </venv>
       <fenv> FEnv </fenv>
       [structural]

  rule <k> V:KResult ~> midEndApply(VEnv, FEnv) => V ... </k>
       <venv> _ => VEnv </venv>
       <fenv> _ => FEnv </fenv>
       [structural]

  syntax KItem ::= midBind(Id)
  rule <k> midConv(P:Id Ps:SList, A:Expr As:SList, VEnv, FEnv) => A ~> midBind(P) ~> midConv(Ps, As, VEnv, FEnv) ... </k>
       [structural]
  rule <k> Val:Expr ~> midBind(P) ~> midConv(Ps, As, VEnv, FEnv) => midConv(Ps, As, VEnv[P <- N +Int 1], FEnv) ... </k>
       <store> Sto => Sto[N +Int 1 <- Val] </store>
       <nextLoc> N => N +Int 1 </nextLoc>
       [structural]

  rule <k> midConv(.SList, .SList, VEnv, FEnv) => .K ... </k>
       <venv> _ => VEnv </venv>
       <fenv> _ => FEnv </fenv>
       [structural]


  // ===
  // top level
  // ===
  syntax KItem ::= "ignoreVal"
  rule <k> %toplevel (E:Expr)Es:SList => E ~> ignoreVal ~> %toplevel Es ... </k>    [structural]
  rule <k> %toplevel .SList => .K ... </k>                                          [structural]

  rule <k> V:KResult ~> ignoreVal => .K ... </k>
       <results> ... .List => ListItem(V) </results>
       [structural]
endmodule