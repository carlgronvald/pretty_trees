﻿// Learn more about F# at http://fsharp.org

module Program

open System
open FsCheck

type Tree<'a> = Node of 'a * Tree<'a> list
//let t = Node('a', [Node('b', [Node('c',[])]); Node('d',[]); Node('e',[Node('f',[])])])
let t = Node('a', [Node('b', [Node('c',[])]); Node('a', [Node('b', [Node('c',[])]); Node('d',[]); Node('e',[Node('f',[])])]); Node('e',[Node('f',[])])])

//let t = Node('a', [Node('b', [Node('a', [Node('b', [Node('c',[])]); Node('d',[]); Node('e',[Node('f',[])])])]); Node('d',[]); Node('e',[Node('f',[])])])

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






/// TODO: EITHER IMPLEMENT OR REMOVE THIS
/// Finds the least right positions of all subtrees with passed extents.
/// Does exactly the opposite of fit_list_right
let fit_list_right_good = List.rev << (List.map (fun x -> -x)) << fit_list_left << (List.map flip_extent) << List.rev

/// DRAWING THE POST-SCRIPT TREE

let get_locations trees = List.map (fun (Node((label, location), subtrees)) -> location) trees 
let get_extends subtrees = (subtrees |> get_locations |> List.max)-(subtrees |> get_locations |> List.min)

let get_width subtrees = if subtrees = [] then 0.0 else get_extends subtrees

let draw_footer = 
    ["stroke\nshowpage"]


let draw_header = 
    ["%!\n<</PageSize[1400 1000]/ImagingBBox null>> setpagedevice\n1 1 scale\n700 999 translate\nnewpath\n/Times-Roman findfont 10 scalefont setfont\n"]


//Functions for drawing the tree:

let draw_horizontal_line position yoffset st = 
    [(string)((position*30.0)-((get_width st)*30.0)/2.0) ; " " ; string(yoffset+(-40));" moveto \n";  
    (string)((position*30.0)+((get_width st)*30.0)/2.0) ; " " ; string(yoffset+(-40));" lineto \n"]
                                                                        
let draw_node_label position yoffset label =
    [(string)(position*30.0);" ";string(yoffset+(-10));
    " moveto \n(";(string)label;
    ") dup stringwidth pop 2 div neg 0 rmoveto show\n";]

let draw_upwards_line position yoffset label =
    [(string)(position*30.0);" ";string((yoffset+10)+(-10));
    " moveto\n";(string)(position*30.0);" ";(string)((yoffset+10)+(0));
    " lineto\n"]


let draw_nodes_and_vertical_lines position yoffset label d =
    if d > 1 then // non-root non-leave
        // This block draws the label 
        //[(string)(position*30.0);" ";string(yoffset+(-10));
        //" moveto \n(";(string)label;
        //") dup stringwidth pop 2 div neg 0 rmoveto show\n";
        (draw_node_label position yoffset label)@
        (draw_upwards_line position yoffset label)@

        // This block draws the vertical line downwards
        (string)(position*30.0);" ";string(yoffset+(-15));
        " moveto\n";(string)(position*30.0);" ";(string)(yoffset+(-30));
        " lineto\n";

        // This block draws the vertical line upwards
        //(string)(position*30.0);" ";string((yoffset+10)+(-10));
        //" moveto\n";(string)(position*30.0);" ";(string)((yoffset+10)+(0));
        //" lineto\n"]
    else 
        // This block draws the label for the root 
        [(string)(position*30.0);" ";string(yoffset+(-25));
        " moveto \n(";(string)label;
        ") dup stringwidth pop 2 div neg 0 rmoveto show\n";

        // This block draws the vertical line downwards
        (string)(position*30.0);" ";string(yoffset+(-30));
        " moveto\n";(string)(position*30.0);" ";(string)(yoffset+(-40));
        " lineto\n"]

let draw_leaf position yoffset label = 
    [(string)(position*30.0);" ";string(yoffset+(-10));
    " moveto \n(";(string)label;
    ") dup stringwidth pop 2 div neg 0 rmoveto show\n";

    (string)(position*30.0);" ";string((yoffset+10)+(-10));
    " moveto\n";(string)(position*30.0);" ";(string)((yoffset+10)+(20));
    " lineto\n"]

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
        let yoffset = depth*(-50);
        match tree with 
        |  (Node((label, position:float),[]))  -> draw_leaf position yoffset label
        |  (Node((label, position:float),st))  -> if (get_width st <> 0.0) then 
                                                        (draw_horizontal_line position yoffset st)@
                                                        (draw_nodes_and_vertical_lines position yoffset label depth)
                                                        @(List.fold (fun s t -> s@(treeToList_inner t (depth+1))) [] st)
                                                    else 
                                                        (draw_nodes_and_vertical_lines position yoffset label depth)
                                                        @(List.fold (fun s t -> s@(treeToList_inner t (depth+1))) [] st) 
    //"Glueing" the ps header and the footer to the generated ps code    
    draw_header @ treeToList_inner tree 1 @ draw_footer

let TreeToPsSlow    = treeToList >> List.fold (fun a b -> a+b) "" 
let TreeToPsFast    = treeToList >> String.concat ""
 
[<EntryPoint>]
let main argv =
    printfn ""
    let k = design t
    let absolut_tree = absolute_positioned_tree k
    (*
    //printfn "positioned tree: %A" k'

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
    *)
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

    
    //printfn "%A" tree_string

    //printfn "\n\n"

    //printfn "%A" tree_string_fast
    1

