// Learn more about F# at http://fsharp.org



module Program

open System
open FsCheck
open System.IO

module AST =

    // Michael R. Hansen 04-06-2021
    // This file is obtained by an adaption of the file MicroC/Absyn.fs by Peter Sestoft
    //

    type Exp =                            
             | N  of int                   (* Integer constant            *)
             | B of bool                   (* Boolean constant            *)
             | Access of Access            (* x    or  ^p    or  a[e]     *)
             | Addr of Access              (* &x   or  &p^   or  &a[e]    *)
             | Apply of string * Exp list  (* Function application        *)

    and Access = 
              | AVar of string             (* Variable access        x    *) 
              | AIndex of Access * Exp     (* Array indexing         a[e] *)
              | ADeref of Exp              (* Pointer dereferencing  p^   *)

    type Stm  =                            
              | PrintLn of Exp               (* Print                          *) 
              | Ass of Access * Exp          (* x:=e  or  p^:=e  or  a[e]:=e   *)
              | Return of Exp option         (* Return from function           *)   
              | Alt of GuardedCommand        (* Alternative statement          *) 
              | Do of GuardedCommand         (* Repetition statement           *) 
              | Block of Dec list * Stm list (* Block: grouping and scope      *)
              | Call of string * Exp list    (* Procedure call                 *)
               
    and GuardedCommand = GC of (Exp * Stm list) list (* Guarded commands    *)

    and Dec = 
             | VarDec of Typ * string        (* Variable declaration               *)
             | FunDec of Typ option * string * Dec list * Stm
                                             (* Function and procedure declaration *) 

    and Typ  = 
             | ITyp                          (* Type int                    *)
             | BTyp                          (* Type bool                   *)
             | ATyp of Typ * int option      (* Type array                  *)
             | PTyp of Typ                   (* Type pointer                *)
             | FTyp of Typ list * Typ option (* Type function and procedure *)

    type Program = P of Dec list * Stm list   (* Program                 *)


type Tree<'a> = Node of 'a * Tree<'a> list
exception NodeNoChildren of string 

// Extent contains 1: leftmost location and 2: rightmost location in each row
type Extent = (float * float) list

// Tree positioning functions
let rmax (p:float) (q:float) :float  =
    if p > q then p else q

let move_extent ((es:Extent),(x:float)) : Extent = List.map ( fun (p,q) -> (p+x, q+x)) es
let flip_extent (e : Extent) = List.map(fun (p,q) -> (-p, -q)) e
let move_tree (Node((label, x), subtrees) , (xprime:float)) =
    Node((label, x+xprime), subtrees)

let rec merge ps qs =
    match (ps,qs) with
    | ([], qs) -> qs
    | (ps, []) -> ps
    | (((p,_)::ps), ((_,q)::qs)) -> (p,q) :: merge ps qs

let merge_list es = List.fold merge [] es

// find the least left offset of the extent l2.
let rec fit (l1:Extent) (l2:Extent) =
    match (l1,l2) with
    | (((_,p)::ps), ((q,_)::qs)) ->
        rmax (fit ps qs) (p-q+1.0)
    | (_,_) ->
        0.0

let fit_list_left es =
    let rec fit_list_inner acc es =
        match es with
        | (e::es) ->
            let x = fit acc e;
            x :: fit_list_inner (merge acc (move_extent (e,x))) es
        | [] -> []
    fit_list_inner [] es

let fit_list_right es =
    let rec fit_list_inner acc es =
        match es with
        | (e::es) ->
            let x = -(fit e acc);
            x :: fit_list_inner (merge (move_extent (e,x)) acc) es
        | [] -> []
    List.rev (fit_list_inner [] (List.rev es))


let mean (x,y) = (x+y)/2.0
/// The mean of right fitting and left fitting gives us a perfectly symmetric fit.
let fit_list es = List.map mean (List.zip (fit_list_left es) (fit_list_right es))



/// Returns a positioned tree where all nodes have a location
let design tree =
    let rec design_inner (Node(label, subtrees)) =
        let (trees, extents) = List.unzip (List.map design_inner subtrees)
        let positions = fit_list extents
        let ptrees = List.map move_tree (List.zip trees positions)
        let pextents = List.map move_extent (List.zip extents positions)
        let resultextent = (0.0,0.0) :: merge_list pextents
        let resulttree = Node((label, 0.0), ptrees)
        (resulttree, resultextent)

    design_inner tree |> fst


// FSCHECK/VERIFICATION FUNCTIONS //
// Criterion 1 functions

/// Converts a relatively positioned tree to an absolutely positioned tree 
let absolute_positioned_tree postree =
    let rec helper (Node((label, position), ts)) (translation:float) =
        Node((label, position+translation), (List.map (fun t -> helper t (translation+position) ) ts))
    helper postree 0.0

/// Do a breadth first search by level
/// Returns a list of lists of nodes, where each list is one level.
let level_bfs tree =
    // The concept is to keep a list of nodes to be traversed both for the 
    // current level and the next level. Then, when the current level is 
    // empty, the current accumulator is appended to the total accumulator
    // (The current accumulator keeps a list of labels, the total
    // keeps a list of lists of labels)
    let rec helper current_level next_level acc acc_old =
        match current_level with
        | [] -> //Case where the current level is empty, and we go on to the next level
            match next_level with
            | [] -> acc_old @ [acc]
            | _ -> helper next_level [] [] (acc_old @ [acc])
        | Node(x, ts)::rest -> //Case where the current level is not empty, so we continue in the current level
            helper rest (next_level@ts) (acc @ [x]) acc_old
    helper [tree] [] [] []


let rec verify_level level =
    match level with 
    | [] -> true
    | (node,pos)::[] -> true
    | (node1,pos1)::(node2,pos2)::rest -> (pos1 <= (pos2 - 1.0)) && (verify_level ((node2,pos2)::rest))

// Check one level at a time
let check_positions postree =
    let rec helper levels =
        match levels with
        | [] -> true
        | level::rest -> verify_level level && helper rest

    let bfs_levels = level_bfs postree
    helper bfs_levels



// Criterion 2 functions
let extractLocations trees = List.map (fun (Node((label, location), subtrees)) -> location) trees

let extractMean subtrees = ((subtrees |> extractLocations |> List.max)+(subtrees |> extractLocations |> List.min))/2.0

let mean_pos_of_children abs_postree =
    match abs_postree with
    | (Node((v,abs_pos),[])) -> raise (NodeNoChildren ("This node has no children"))
    | (Node((v,abs_pos),st)) -> extractMean st

let rec validate_children_positions abs_postree =
    match abs_postree with
    | (Node((v,abs_pos),[])) -> true // No children, must be centered correctly
    | (Node((v,abs_pos),st)) -> // Check that mean of subtree node positions equals abs_pos
            abs(abs_pos-(mean_pos_of_children abs_postree)) < 0.0000001 && // Avoid float rounding errors
            List.fold (fun acc elem -> acc && (validate_children_positions elem)) true st




// Criterion 3 functions
let rec reflect (Node(v, subtrees)) =
    Node(v, List.map reflect (List.rev subtrees))

let rec reflectpos (Node((v,x : float), subtrees)) =
    Node((v, -x), List.map reflectpos subtrees)

    
// Criterion 4 functions
let preorder tree =
    let rec helper depth subtree =
        match subtree with
        | Node(_, []) -> 
            [depth]
        | Node(_, ts) ->
            depth :: List.collect (helper (depth+1)) ts
    helper 0 tree

let flat_bfs tree =
    let rec helper next acc =
        match next with
        | [] -> acc
        | Node(x, ts)::rest ->
            helper (rest@ts) (Node(x,ts)::acc)
    helper [tree] []

let matching_pairs pairs = List.fold (fun s (x,y) -> s && x = y) true pairs

let matching_preorder given_preorder node =
    preorder node = given_preorder




/// Returns whether two subtrees are designed in the same way
let same_design (Node(_,subtrees_1)) (Node(_,subtrees_2)) =
    let extract_design trees = (List.map (fun (Node((v,p),ts)) -> p) (flat_bfs trees))
    let pairs = List.zip (List.collect extract_design subtrees_1) (List.collect extract_design subtrees_2)
    matching_pairs pairs

//let positioned_tree = design t
//let preorder_filtered = 
//let designs = List.map (same_design positioned_tree) preorder_filtered
let all_equivalent_subtrees_match positioned_tree positioned_subtree =
    let equivalent_trees = List.filter (matching_preorder (preorder positioned_subtree)) (flat_bfs positioned_tree)
    let matching_designs = List.map (same_design positioned_subtree) equivalent_trees
    List.reduce (&&) matching_designs

let get_locations trees = List.map (fun (Node((label, location), subtrees)) -> location) trees 
let get_extends subtrees = (subtrees |> get_locations |> List.max)-(subtrees |> get_locations |> List.min)

let get_width subtrees = if subtrees = [] then 0.0 else get_extends subtrees



(*======================LABEL SPLITTING BEGIN======================================*)
let calculateLines (s) : int = int(((string)s).Length/8)

// split according to 
let string2Words s =
    let split s = 
        let rec scan s i =
            if ((string)s).Length = 0 then []
            elif (i+1)%8 = 0 then [((string)s).[..i]; ((string)s).[i+1..]]
            elif i = (((string)s).Length - 1) then [((string)s)]
            else scan ((string)s) (i+1)
        scan s 0
    let rec fold acc s =
        match split ((string)s) with
        | [x] -> acc @ [x]
        | [head;tail] -> fold (acc @ [head]) tail
        | _ -> acc
    fold [] ((string)s)

// Split according to the space  
let string2WordsSpace s =
    let split s =
        let rec scan (s) i =
            if ((string)s).Length = 0 then []
            elif ((string)s).[i] = ' ' && i = 0 then scan ((string)s).[i+1..] 0
            elif ((string)s).[i] = ' ' then [((string)s).[..i-1]; ((string)s).[i+1..]]
            elif i = (((string)s).Length - 1) then [s]
            else scan ((string)s) (i+1)
        scan s 0
    let rec fold acc s =
        match split s with
        | [x] -> acc @ [x]
        | [head;tail] -> fold (acc @ [head]) tail
        | _ -> acc
    fold [] s

// let addNextLineToString (list:list<'a>) =
//     String.concat "\n" list
    
(*======================LABEL SPLITTING END======================================*)



//Functions for drawing the tree:
let draw_footer = 
    ["stroke\nshowpage"]


let draw_header = 
    ["%!\n<</PageSize[1400 1000]/ImagingBBox null>> setpagedevice\n1 1 scale\n700 999 translate\nnewpath\n/Times-Roman findfont 5 scalefont setfont\n"]

let draw_horizontal_line position yoffset st = 
    [(string)((position*30.0)-((get_width st)*30.0)/2.0) ; " " ; string(yoffset+(-40.0));" moveto \n";  
    (string)((position*30.0)+((get_width st)*30.0)/2.0) ; " " ; string(yoffset+(-40.0));" lineto \n"]

let draw_node_label position yoffset label d =
    [(string)(position*30.0);" ";string(yoffset+(float)d);
    " moveto \n(";(string)label;
    ") dup stringwidth pop 2 div neg 0 rmoveto show\n";]

let draw_vertical_line position yoffset d1 d2 =
    [(string)(position*30.0);" ";string(yoffset+(float)d1);
    " moveto\n";(string)(position*30.0);" ";(string)((yoffset+(float)d2));
    " lineto\n"]
                                                                        

let draw_node position yoffset label d =
    let label_list = string2Words label
    let label_list_draw_ps_not_root label_list = List.mapi (fun i label ->
        (draw_node_label position yoffset label (-5.0 * (float) i))) label_list

    let label_list_draw_ps_root label_list = List.mapi (fun i label ->
        (draw_node_label position yoffset label (-15.0 - 5.0 * (float) i))) label_list

    if d > 1 then // non-root non-leaf
        List.concat(label_list_draw_ps_not_root label_list )@
            (draw_vertical_line position yoffset (2.5 - 5.0 * (float) label_list.Length) -40.0) @
            (draw_vertical_line position yoffset 5.0 10.0)
    else 
        List.concat(label_list_draw_ps_root label_list )@
            (draw_vertical_line position yoffset (-12.0 - 5.0 * (float)label_list.Length) -40.0)

let draw_leaf position yoffset label =
    let label_list = string2Words label
    let label_list_draw_ps label_list = List.mapi (fun i label ->
        (draw_node_label position yoffset label (-5.0 * (float) i))) label_list
    
    List.concat(label_list_draw_ps label_list )@
    (draw_vertical_line position yoffset 5.0 10.0)

// Generates a large tree for testing the timing of the different implementations
let rec generate_test_tree n =
    match n with
    | 0 -> Node(0, [])
    | _ -> Node(0, [generate_test_tree (n-1);generate_test_tree (n-1)])

//Converting a positioned tree to a list of strings
let treeToList tree =
    // Inner function that recu rsively draws the tree,
    // the depth argument is our way of keeping track 
    // of the depth of the current node in the tree
    let rec treeToList_inner tree (depth:int) =
        let yoffset = (float)depth*(-50.0);
        match tree with 
        |  (Node((label, position:float),[]))  -> draw_leaf position yoffset label
        |  (Node((label, position:float),st))  -> if (get_width st <> 0.0) then 
                                                        (draw_horizontal_line position yoffset st)@
                                                        (draw_node position yoffset label depth)
                                                        @(List.fold (fun s t -> s@(treeToList_inner t (depth+1))) [] st)
                                                    else 
                                                        (draw_node position yoffset label depth)
                                                        @(List.fold (fun s t -> s@(treeToList_inner t (depth+1))) [] st) 
    //"Glueing" the ps header and the footer to the generated ps code    
    draw_header @ treeToList_inner tree 1 @ draw_footer

let TreeToPsSlow    = treeToList >> List.fold (fun a b -> a+b) "" 
let TreeToPsFast    = treeToList >> String.concat ""
 
open AST

/// Parses a type in the AST
let rec parse_type (typ:Typ) =
    match typ with
    | ITyp -> Node("Int", [])
    | BTyp -> Node("Bool",[])                (* Type bool                   *)
    | ATyp(typ:Typ, None) -> Node("Array", [parse_type typ])      (* Type array                  *)
    | ATyp(typ:Typ, Some(len)) -> Node("Array", [(parse_type typ); Node("length "+ (string)len, [])]);
    | PTyp(typ:Typ) -> Node("Pointer", [parse_type typ])                   (* Type pointer                *)
    | FTyp(types:Typ list, output) ->
        let onode = match output with
                    |Some(output) -> [Node("Output",[parse_type output])]
                    |None -> []
        Node("Function", onode @ (List.map parse_type types) ) (* Type function and procedure *)

/// Parses a variable, array, or pointer access element in the AST
let rec parse_access access =
    match access with
    | AVar(name) -> Node("AVar", [Node("Var '" + name + "'", [])])              (* Variable access        x    *) 
    | AIndex(acc, exp) -> Node("AIndex", [parse_access acc;parse_expression exp])     (* Array indexing         a[e] *)
    | ADeref(exp) -> Node("ADeref", [parse_expression exp])              (* Pointer dereferencing  p^   *)

/// Parses an expression in the AST
and parse_expression expression = 
    match expression with
    | N(i) -> Node("Int "+(string)i, [])                   (* Integer constant            *)
    | B(b) -> Node("Bool "+(string)b, [])                    (* Boolean constant            *)
    | Access(access) -> parse_access access           (* x    or  ^p    or  a[e]     *)
    | Addr(access) -> Node("Addr", [parse_access access])              (* &x   or  &p^   or  &a[e]    *)
    | Apply(function_name, exps) -> Node("Apply", Node(function_name, [])::(List.map parse_expression exps))  (* Function application        *)

/// Parses a statement in the AST
let rec parse_statement statement =
    match statement with
    | PrintLn(exp) -> Node("PrintLn", [parse_expression exp])               (* Print                          *) 
    | Ass(access, exp) -> Node("Ass", [parse_access access; parse_expression exp])          (* x:=e  or  p^:=e  or  a[e]:=e   *)
    | Return(exp) -> 
        let rnode = match exp with
                    | Some(exp) -> [parse_expression(exp)]
                    | None -> []
        Node("Return", rnode)        (* Return from function           *)
    | Alt(gc) -> Node("Alt", [parse_guarded_command gc])(* Alternative statement          *)
    | Do(gc) -> Node("Do", [parse_guarded_command gc])         (* Repetition statement           *)
    | Block(declarations, statements) -> (* Block: grouping and scope      *)
        Node("Block", (List.map parse_declaration declarations)@(List.map parse_statement statements))
    | Call(name, expressions) -> (* Procedure call                 *)
        Node("Call", Node(name, [])::(List.map parse_expression expressions)) 

/// Parses a GC in the AST
and parse_guarded_command (GC( cmdlist)) =
    Node("GC", List.map (fun (exp,stmts) -> Node("If", [(parse_expression exp);(Node("Then", List.map parse_statement stmts))])) cmdlist)

/// Parses a declaration of either a function or a variable in the AST
and parse_declaration (declaration:Dec) =
    match declaration with
    | (VarDec(typ, name)) ->
        (Node("VarDec", [Node(name, []);parse_type typ]))
    | FunDec(typ, name, declarations, statement) ->
        let tnode = match typ with
                    | Some(typ) -> [parse_type(typ)]
                    | None -> []
        (Node("FunDec", tnode @ [Node(name,[])] @ (List.map parse_declaration declarations) @ [parse_statement statement]))

/// Converts a Program to a Tree<String> so that it is ready for rendering.
let toGeneralTree (P(declarations, statements)) =
    let declarations = List.map parse_declaration declarations
    let statements = List.map parse_statement statements
    Node("Program", declarations@statements)

let it : Program =
  P ([VarDec (ITyp,"x")],
     [Ass (AVar "x",N 1);
      Do
        (GC
           [(Apply ("=",[Access (AVar "x"); N 1]),
             [PrintLn (Access (AVar "x"));
              Ass (AVar "x",Apply ("+",[Access (AVar "x"); N 1]))]);
            (Apply ("=",[Access (AVar "x"); N 2]),
             [PrintLn (Access (AVar "x"));
              Ass (AVar "x",Apply ("+",[Access (AVar "x"); N 1]))]);
            (Apply ("=",[Access (AVar "x"); N 3]),
             [PrintLn (Access (AVar "x"));
              Ass (AVar "x",Apply ("+",[Access (AVar "x"); N 1]))])]);
      PrintLn (Access (AVar "x"))])

let tree = toGeneralTree it

//printfn "%A" (toGeneralTree it)
TreeToPsFast (absolute_positioned_tree (design tree)) |> ignore
open System.IO
let pos_tree_to_file path postree =
    File.WriteAllText (path, TreeToPsSlow (absolute_positioned_tree postree)) 

let tree_to_file path tree =
    pos_tree_to_file path (design tree)


[<EntryPoint>]
let main argv =
    let t = Node("1", [Node("a", [Node("sdadqwqeqweqwe",[])]); Node("sadasdasdasds", [Node("b", [Node("sadsadasdsads",[])]); Node("sssssssssssssssssss",[]); Node("eeeeeeeeeeeeeeeeee",[Node("ffffffffffffffffff",[])])]); Node("dsaoooooooooooooooo",[Node("kkkkkkkkkkkkkkkkkk",[])])])
    let k = design t
    let absolut_tree = absolute_positioned_tree k

    let tree_string = TreeToPsSlow absolut_tree
    // // printfn "%A" (draw_header+tree_string+draw_footer)
    // File.WriteAllText("./generated_file.ps", tree_string)
    printfn "%A" tree_string

    tree_to_file "../../../../output.ps" tree
    printfn "Output a tree!"
    
    (*
    // FSCHECK: Criterion 1
    printfn "\n\nFsCheck Criterion 1 test:"
    let check_criterion1 test_tree = check_positions (absolute_positioned_tree (design test_tree))
    Check.Quick check_criterion1

    // FSCHECK: Criterion 2
    printfn "\n\nFsCheck Criterion 2 test:"
    let check_criterion2 test_tree = validate_children_positions (absolute_positioned_tree (design test_tree))
    Check.Quick check_criterion2

    // FSCHECK: Criterion 3
    printfn "\n\nFsCheck Criterion 3 test:"
    let check_criterion3 test_tree =
        let ds = design test_tree
        let ref_ds = (test_tree |> reflect |> design |> reflectpos |> reflect )
        let extract_design designed = designed |> flat_bfs |> List.map (fun (Node((v2,p2),ts)) -> (v2,p2))
        let pairs = List.zip (ds |> extract_design) (ref_ds |> extract_design)
        matching_pairs pairs
    Check.Quick check_criterion3

    printfn "\n\nFsCheck Criterion 4 test:"
    let check_criterion4 test_tree =
        let designed = design test_tree
        let equivs_that_match = List.map (all_equivalent_subtrees_match designed) (flat_bfs designed)
        List.reduce (&&) equivs_that_match
    
    Check.Quick check_criterion4
    let test_tree           = generate_test_tree 10
    let designed_test_tree  = design test_tree
    let designed_absolute_test_tree = absolute_positioned_tree designed_test_tree

    let stopWatch           = System.Diagnostics.Stopwatch.StartNew()
    let tree_string         = TreeToPsSlow designed_absolute_test_tree
    printfn "Slow time %f" stopWatch.Elapsed.TotalMilliseconds
    stopWatch.Stop()

    let stopWatch_1           = System.Diagnostics.Stopwatch.StartNew()
    let tree_string_fast      = TreeToPsFast designed_absolute_test_tree
    stopWatch_1.Stop()
    printfn "Fast time %f" stopWatch_1.Elapsed.TotalMilliseconds
    *)
    
    1

