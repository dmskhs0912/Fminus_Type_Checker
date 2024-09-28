namespace FMinus

open AST

// Type.infer() must raise this if the input program seems to have a type error.
exception TypeError

// The types available in our F- language.
type Type =
  | Int
  | Bool
  | TyVar of string
  | Func of Type * Type

type TypeEnv = Map<string, Type>

// Substitution
type Subst = Map<string, Type>

// type equations
type TypeEqtn = List<Type * Type>

module Type =

  // Convert the given 'Type' to a string.
  let rec toString (typ: Type): string =
    match typ with
    | Int -> "int"
    | Bool -> "bool"
    | TyVar s -> s
    | Func (t1, t2) -> sprintf "(%s) -> (%s)" (toString t1) (toString t2)

  // Generate new Type variable with fresh name.
  // It starts with "a".
  let generateTypeVar = 
    let count = ref 0
    fun () ->
      let varName = sprintf "a%d" !count
      incr count 
      TyVar varName

  // Generate new Type variable for operands of = and <>. (It must be Int or Bool)
  // It starts with "b".
  let specialTypeVar = 
    let count = ref 0
    fun () ->
      let varName = sprintf "b%d" !count
      incr count
      TyVar varName

  // Generate type equations
  let rec gen (env: TypeEnv) (exp: Exp) (t: Type) (eqtn: TypeEqtn) : TypeEqtn = 
    match exp with
    | Num n -> (t, Int) :: eqtn
    | True -> (t, Bool) :: eqtn
    | False -> (t, Bool) :: eqtn
    | Var x -> 
      if Map.containsKey x env
      then (t, Map.find x env) :: eqtn
      else raise TypeError
    
    | Neg e ->
      let newEqtn = gen env e Int eqtn
      (t, Int) :: newEqtn    // (t = Int) ^ Gen(Gamma, e, Int)
    
    | Add (e1, e2) ->
      let eqtn1 = gen env e1 Int eqtn
      let eqtn2 = gen env e2 Int eqtn1
      (t, Int) :: eqtn2

    | Sub (e1, e2) ->
      let eqtn1 = gen env e1 Int eqtn
      let eqtn2 = gen env e2 Int eqtn1
      (t, Int) :: eqtn2
    
    | LessThan (e1, e2) ->
      let eqtn1 = gen env e1 Int eqtn
      let eqtn2 = gen env e2 Int eqtn1
      (t, Bool) :: eqtn2

    | GreaterThan (e1, e2) ->
      let eqtn1 = gen env e1 Int eqtn
      let eqtn2 = gen env e2 Int eqtn1
      (t, Bool) :: eqtn2

    | Equal (e1, e2) -> 
      let tyVar1 = specialTypeVar ()
      let tyVar2 = specialTypeVar ()
      let eqtn1 = gen env e1 tyVar1 eqtn
      let eqtn2 = gen env e2 tyVar2 eqtn1
      (tyVar1, tyVar2) :: ((t, Bool) :: eqtn2)

    | NotEq (e1, e2) -> 
      let tyVar1 = specialTypeVar ()
      let tyVar2 = specialTypeVar ()
      let eqtn1 = gen env e1 tyVar1 eqtn
      let eqtn2 = gen env e2 tyVar2 eqtn1
      (tyVar1, tyVar2) :: ((t, Bool) :: eqtn2)

    | IfThenElse (e1, e2, e3) ->
      let eqtn1 = gen env e1 Bool eqtn
      let eqtn2 = gen env e2 t eqtn1
      let eqtn3 = gen env e3 t eqtn2
      eqtn3

    | LetIn (x, e1, e2) ->
      let tyVar = generateTypeVar ()
      let eqtn1 = gen env e1 tyVar eqtn
      let eqtn2 = gen (Map.add x tyVar env) e2 t eqtn1
      eqtn2

    | LetFunIn (f, x, e1, e2) ->
      let ta = generateTypeVar ()
      let tr = generateTypeVar ()
      let eqtn1 = gen (Map.add x ta env) e1 tr eqtn
      let eqtn2 = gen (Map.add f (Func (ta, tr)) env) e2 t eqtn1
      eqtn2

    | LetRecIn (f, x, e1, e2) ->
      let ta = generateTypeVar ()
      let tr = generateTypeVar ()
      let env1 = Map.add f (Func (ta, tr)) env
      let eqtn1 = gen (Map.add x ta env1) e1 tr eqtn
      let eqtn2 = gen env1 e2 t eqtn1
      eqtn2

    | Fun (x, e) ->
      let ta = generateTypeVar ()
      let tr = generateTypeVar ()
      let eqtn1 = gen (Map.add x ta env) e tr eqtn
      (t, Func (ta, tr)) :: eqtn1

    | App (e1, e2) ->
      let ta = generateTypeVar ()
      let eqtn1 = gen env e1 (Func (ta, t)) eqtn
      let eqtn2 = gen env e2 ta eqtn1
      eqtn2

  // Return true if type variable occurs in t.
  let rec occursCheck (tv: string) (t:Type) : bool=
    match t with
    | TyVar x -> x = tv
    | Func (t1, t2) -> occursCheck tv t1 || occursCheck tv t2
    | _ -> false

  // Replace tv into newType if typ contains tv.
  let rec replaceTypeVar (tv: string) (newType:Type) (typ: Type) : Type =
    match typ with
    | Int -> Int
    | Bool -> Bool
    | TyVar x -> if x = tv then newType else typ
    | Func (t1, t2) -> Func (replaceTypeVar tv newType t1, replaceTypeVar tv newType t2)

  // Apply the function replaceTypeVar to values in s and return it  
  let replaceSubst (tv: string) (newType: Type) (s: Subst) : Subst =
    s |> Map.map (fun _ typ -> replaceTypeVar tv newType typ)

  let rec app (s: Subst) (t: Type) : Type =
    match t with
    | Int -> Int
    | Bool -> Bool
    | TyVar tv ->
      if Map.containsKey tv s
      then Map.find tv s
      else TyVar tv
    | Func (t1, t2) -> Func (app s t1, app s t2)

  let rec unify ((t1, t2): Type * Type) (s: Subst) : Subst =
    extend (app s t1, app s t2) s 
  
  and extend (eq: Type * Type) (s: Subst) : Subst =
    match eq with
    | (Int, Int) -> s
    | (Bool, Bool) -> s
    | (Func (tx1, ty1), Func (tx2, ty2)) ->
      unify (ty1, ty2) (extend (tx1, tx2) s)
    | (TyVar tv, t) | (t, TyVar tv) ->
      if t = TyVar tv
      then s
      else if occursCheck tv t then raise TypeError
      else Map.add tv t (replaceSubst tv t s)
    | _ -> raise TypeError

  // Return true if all operands of = and <> is Int or Bool.
  let intboolCheck (s: Subst) : bool =
    s |> Map.forall (fun key value -> 
      not (key.StartsWith("b")) || (value = Int || value = Bool))

  // Return the inferred type of the input program.
  let infer (prog: Program) : Type =
    let tp = TyVar "tp"
    let eqtns = gen Map.empty prog tp List.empty
    let rec appUnify (equations: TypeEqtn) (s: Subst) : Subst =
      match equations with
      | [] -> s
      | head :: tail -> appUnify tail (unify head s)

    let finalSubst = appUnify eqtns Map.empty
    if intboolCheck finalSubst then Map.find "tp" finalSubst else raise TypeError