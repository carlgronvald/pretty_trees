// Learn more about F# at http://fsharp.org

module Program

open System
open FsCheck


type Tree<'a> = Node of 'a * Tree<'a> list
// Extent contains 1: leftmost location and 2: rightmost location in each row
type Extent = (float * float) list

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

/// 
/// Finds the least left position of all subtrees with individual extents es.
/// 
/// es is a list of extents
let fit_list_left es =
    let rec fit_list_inner acc es =   
        match es with
        | (e::es) ->
            let x = fit acc e;
            x :: fit_list_inner( (merge acc (move_extent (e,x)))) es
        | [] -> []
    fit_list_inner [] es


/// Finds the least right positions of all subtrees with passed extents.
/// Does exactly the opposite of fit_list_right
let fit_list_right = List.rev << List.map (fun x -> -x) << fit_list_left << List.map flip_extent << List.rev

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



let t = Node('a', [Node('b', [Node('c',[])]); Node('d',[]); Node('e',[Node('f',[])])])

let absolute_positioned_tree postree =
    let rec helper (Node((label, position), ts)) (translation:float) =
        (label, position+translation) :: (List.collect (fun t -> helper t (translation+position) ) ts)
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

let tt = Node('a', [Node('b', [Node('d', []); Node('e', []); Node('f', [])]); Node('c', [])])
let b2 = level_bfs tt
printf "level bfs %A" b2
let rpt = design tt
let apt = absolute_positioned_tree rpt
printf "absolutely positioned tree %A" apt
[<EntryPoint>]
let main argv =
    printfn ""
    let k = design t
    printf "positioned tree: %A" k

    1

