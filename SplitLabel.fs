open System
let calculateLines (str:String) : int = int(str.Length/8)

let string2Words s =
    let split s = 
        let rec scan (s:string) i =
            if s.Length = 0 then []
            elif (i+1)%8 = 0 then [s.[..i]; s.[i+1..]]
            elif i = (s.Length - 1) then [s]
            else scan s (i+1)
        scan s 0
    let rec fold acc s =
        match split s with
        | [x] -> acc @ [x]
        | [head;tail] -> fold (acc @ [head]) tail
        | _ -> acc
    fold [] s

// change the very long string to 
let string2WordsSpace s =
    let split s =
        let rec scan (s:string) i =
            if s.Length = 0 then []
            elif s.[i] = ' ' && i = 0 then scan s.[i+1..] 0
            elif s.[i] = ' ' then [s.[..i-1]; s.[i+1..]]
            elif i = (s.Length - 1) then [s]
            else scan s (i+1)
        scan s 0
    let rec fold acc s =
        match split s with
        | [x] -> acc @ [x]
        | [head;tail] -> fold (acc @ [head]) tail
        | _ -> acc
    fold [] s

// let addNextLineToString (list:list<String>):String =
//     let rec loop list acc_string = 
//         match list with
//         | [] -> ""
//         | tail -> acc_string+tail
//         | _ -> acc_string+
    

let sum list =
   let rec loop list acc =
       match list with
       | head :: tail -> loop tail (acc + head)
       | [] -> acc
   loop list 0

let rec printList listx =
        match listx with
        | head :: tail -> printf "%d " head; printList tail
        | [] -> printfn ""


[<EntryPoint>]
let main argv =

    let str1 = "    asdqweasdqweas dqweasdqwweasdqwe"
    // // length: 30 
    // printfn "" 
    // let maxLengthPerLine = 8
    // let 
    // printfn "%d" (calculateLines str1)
    // let list1 = [ 1; 5; 100; 450; 788 ]
    // printList str1
    printfn "%A" (string2WordsSpace str1)
    let result = String.concat "\n" (string2WordsSpace str1)
    printfn "%s" result
    1