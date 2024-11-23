import Lean

abbrev Result := Except String

def Option.toResult (err : String) : Option α → Result α
  | some v => .ok v
  | none => .error err

namespace Fn

  -- Syntax

  inductive Ty
    | bool
    | int
  deriving BEq, Repr

  instance : ToString Ty where
    toString t :=
      match t with
        | .bool => "bool"
        | .int => "int"

  inductive BinOp
    | add
    | sub
    | eq

  inductive Exp
    | const : BitVec 32 → Exp
    | var : String → Exp
    | app : String → List Exp → Exp
    | binop : BinOp → Exp → Exp → Exp
    | ite : Exp → Exp → Exp → Exp

  structure Fn where
    name : String
    params : List (String × Ty)
    ret : Ty
    body : Exp

  abbrev Prog := List Fn

  -- Typing rules

  structure Ctx where
    vars : Std.HashMap String Ty
    fns : Std.HashMap String (List Ty × Ty)

  def Ctx.empty : Ctx :=
    ⟨.empty, .empty⟩

  def BinOp.ty (x y : Ty) : BinOp → Result Ty
    | add | sub =>
      if x == .int && y == .int then
        .ok .int
      else
        .error s!"arith op with {x} ⊕ {y}"
    | eq =>
      if x == y then
        .ok .bool
      else
        .error s!"eq op with {x} == {y}"

  def Exp.ty (ctx : Ctx) : Exp → Result Ty
    | const _ => .ok .int
    | var name => (ctx.vars.get? name).toResult s!"var '{name}' not found"
    | app f args => do
      let sig ← (ctx.fns.get? f).toResult s!"fn '{f}' not found"
      let rec map (es : List Exp) : Result (List Ty) :=
        match es with
        | [] => .ok []
        | h :: t => do
          let h ← Exp.ty ctx h
          let t ← map t
          .ok (h :: t)
      let args ← map args
      if args == sig.fst then
        .ok sig.snd
      else
        .error s!"args {args} doesn't match sig {sig.fst}"
    | binop bop x y => do
      let x ← x.ty ctx
      let y ← y.ty ctx
      bop.ty x y
    | ite cond tt ff => do
      let cond ← cond.ty ctx
      let tt ← tt.ty ctx
      let ff ← ff.ty ctx
      if cond != .bool then
        .error s!"ite cond == {cond}"
      else if tt != ff then
        .error s!"ite branches {tt} != {ff}"
      else
        .ok tt

    def Exp.recurses (self : String) : Exp → Bool
      | const _ | var _ => false
      | app name args =>
        if name == self then
          true
        else
          let rec map : List Exp → List Bool
            | [] => []
            | h :: t => h.recurses self :: map t
          (map args).foldl or false
      | binop _ x y => x.recurses self || y.recurses self
      | ite cond tt ff =>
        cond.recurses self || tt.recurses self || ff.recurses self

    def Exp.onlyTailRecursion (self : String) : Exp → Bool
      | const _ | var _ => true
      | app name args =>
        if name == self then
          let args_rec := args.map (Exp.recurses self)
          let any_args_rec := args_rec.foldl or false
          !any_args_rec
        else
          let rec map : List Exp → List Bool
            | [] => []
            | h :: t => h.onlyTailRecursion self :: map t
          let args_only_tail := map args
          args_only_tail.foldl and true
      | binop _ x y => !x.recurses self && !y.recurses self
      | ite cond tt ff =>
        !cond.recurses self && tt.onlyTailRecursion self && ff.onlyTailRecursion self

    def Fn.ty (ctx : Ctx) (fn : Fn) : Result Fn := do
      let vars : Std.HashMap String Ty :=
        fn.params.foldl (λ vars (name, t) => vars.insert name t) .empty
      let ctx := {ctx with vars := vars}
      let ret ← fn.body.ty ctx
      if ret != fn.ret then
        .error s!"ret doesn't match {ret} != {fn.ret}"
      else if !fn.body.onlyTailRecursion fn.name then
        .error s!"{fn.name} contains non-tail-recursion"
      else
        .ok fn

    def Prog.ty (prog : Prog) : Result (List Ty × Ty) := do
      -- Type check functions from top to bottom
      let _ ← prog.foldlM
        (λ ctx fn =>
          let input_tys := fn.params.map Prod.snd
          let ctx := {ctx with fns := ctx.fns.insert fn.name (input_tys, fn.ret)}
          fn.ty ctx >>= λ _ => .ok ctx
          )
        .empty
      let main ← (prog.find? (·.name == "main")).toResult "no main function found"
      .ok (main.params.map Prod.snd, main.ret)

  namespace DSL
    open Lean Elab Meta

    ------------ Types ------------
    declare_syntax_cat ty

    syntax "bool" : ty
    syntax "int" : ty

    def elabTy : Syntax → MetaM Expr
      | `(ty| bool) => return .const ``Ty.bool []
      | `(ty| int) => return .const ``Ty.int []
      | _ => throwUnsupportedSyntax

    ------------ Expressions ------------
    declare_syntax_cat args
    declare_syntax_cat exp

    -- Args single
    syntax exp : args
    -- Args app
    syntax exp ", " args : args

    -- Parens
    syntax:100 "(" exp ")" : exp
    -- Int literal
    syntax:100 num : exp
    -- Vars
    syntax:100 ident : exp
    -- App empty
    syntax:100 ident "()" : exp
    -- App
    syntax:100 ident "(" args ")" : exp
    -- BinOps
    syntax:50 exp:50 " + " exp:51 : exp
    syntax:50 exp:50 " - " exp:51 : exp
    syntax:30 exp:30 " == " exp:30 : exp
    -- if then else
    syntax:20 "if " exp:21 " then " exp:0 " else " exp:0 " end" : exp

    def emptyArgs : List Exp := []

    partial def elabExp : Syntax → MetaM Expr
      | `(exp| ( $e:exp )) => elabExp e
      | `(exp| $n:num) => do
        let n ← mkAppM ``BitVec.ofNat #[mkNatLit 32, mkNatLit n.getNat]
        mkAppM ``Exp.const #[n]
      | `(exp| $id:ident) => mkAppM ``Exp.var #[mkStrLit id.getId.toString]
      | `(args| $e:exp) => do
        let e ← elabExp e
        mkAppM ``List.cons #[e, .const ``emptyArgs []]
      | `(args| $h:exp, $t:args) => do
        let h ← elabExp h
        let t ← elabExp t
        mkAppM ``List.cons #[h, t]
      | `(exp| $f:ident()) =>
        let f := mkStrLit f.getId.toString
        let args := .const ``emptyArgs []
        mkAppM ``Exp.app #[f, args]
      | `(exp| $f:ident($as:args)) => do
        let f := mkStrLit f.getId.toString
        let as ← elabExp as
        mkAppM ``Exp.app #[f, as]
      | `(exp| $e1:exp + $e2:exp) => do
        let bop := .const ``BinOp.add []
        let e1 ← elabExp e1
        let e2 ← elabExp e2
        mkAppM ``Exp.binop #[bop, e1, e2]
      | `(exp| $e1:exp - $e2:exp) => do
        let bop := .const ``BinOp.sub []
        let e1 ← elabExp e1
        let e2 ← elabExp e2
        mkAppM ``Exp.binop #[bop, e1, e2]
      | `(exp| $e1:exp == $e2:exp) => do
        let bop := .const ``BinOp.eq []
        let e1 ← elabExp e1
        let e2 ← elabExp e2
        mkAppM ``Exp.binop #[bop, e1, e2]
      | `(exp| if $cond:exp then $then_body:exp else $else_body:exp end) => do
        let cond ← elabExp cond
        let then_body ← elabExp then_body
        let else_body ← elabExp else_body
        mkAppM ``Exp.ite #[cond, then_body, else_body]
      | _ => throwUnsupportedSyntax

    ------------ Functions ------------
    declare_syntax_cat param
    declare_syntax_cat params
    declare_syntax_cat fn_stx

    syntax "(" ident " : " ty ")" : param
    syntax param* : params
    syntax "fn " ident params " : " ty " := " exp " end" : fn_stx

    def elabParam : Syntax → MetaM Expr
      | `(param| ( $name:ident : $t:ty )) => do
        let name := mkStrLit name.getId.toString
        let t ← elabTy t
        mkAppM ``Prod.mk #[name, t]
      | _ => throwUnsupportedSyntax

    def emptyParams : List (String × Ty) := []

    partial def elabParams : Syntax → MetaM Expr
      | `(params| $ps:param*) => do
        let ps ← ps.mapM elabParam
        ps.toList.foldr
          (λ p ps => ps >>= λ ps => mkAppM ``List.cons #[p, ps])
          (return .const ``emptyParams [])
      | _ => throwUnsupportedSyntax

    def elabFn : Syntax → MetaM Expr
      | `(fn_stx| fn $name:ident $ps:params : $ret:ty := $body:exp end) => do
        let name := mkStrLit name.getId.toString
        let ps ← elabParams ps
        let ret ← elabTy ret
        let body ← elabExp body
        mkAppM ``Fn.mk #[name, ps, ret, body]
      | _ => throwUnsupportedSyntax

    ------------ Programs ------------
    declare_syntax_cat prog

    syntax fn_stx+ : prog

    def emptyProg : Prog := []
    def Prog.cons (f : Fn) (p : Prog) : Prog := f :: p

    def elabProg : Syntax → MetaM Expr
      | `(prog| $f:fn_stx $fs:fn_stx*) => do
        let f ← elabFn f
        let fs ← fs.mapM elabFn
        let fs := f :: fs.toList
        fs.foldr
          (λ h t => t >>= λ t => mkAppM ``Prog.cons #[h, t])
          (return .const ``emptyProg [])
      | _ => throwUnsupportedSyntax

    elab p:prog : term => elabProg p

    def add :=
      fn add (x : int) (y : int) : int :=
        if x == 0 then
          y
        else
          add(x - 1, y + 1)
        end
      end

      fn main (x : int) (y : int) : int :=
        add(x, y)
      end

    #eval add.ty

  end DSL

end Fn
