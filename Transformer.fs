module Transformer

open Newtonsoft.Json

exception TransformerException of int * int * string
exception ValidationError of string

type RootNode = { Children: TransformerNode list }

and Assignment =
    { Left: TransformerNode
      Right: TransformerNode }

and FunctionCall = { Args: TransformerNode list }

and TypedIdentifier = { Identifier: string; Type: string }

and Operation =
    { Left: TransformerNode option
      Right: TransformerNode
      Operator: string }

and FunctionBody = TransformerNode list

and FunctionDefinition =
    { Args: FunctionArg list
      Body: FunctionBody }

and TypedFunctionDefinition =
    { Args: FunctionArg list
      Body: FunctionBody
      ReturnType: string }

and FunctionArg =
    { Identifier: string
      Type: string option }

and ObjectProperty =
    | Property of string * TransformerNode
    | Method of string * FunctionDefinition
    | StaticMethod of string * FunctionDefinition
    | StaticProperty of string * TransformerNode

and Object = { Properties: ObjectProperty list }

and MethodCall =
    { Name: string
      Args: TransformerNode list
      Left: TransformerNode }

and PropertyAccess =
    { Left: TransformerNode; Value: string }

and AccessNode =
    | MethodCall of MethodCall
    | PropertyAccess of PropertyAccess

and AccessChain = AccessNode list

and TransformerNode =
    | RootNode of RootNode
    | Import of string
    | Identifier of string
    | TypedIdentifierNode of TypedIdentifier
    | String of string
    | PointerIdentifier of string
    | DeRefIdentifier of string
    | Number of string
    | OperatorExpression of Operation list
    | Operator of string
    | BoolExpression of string
    | AssignmentNode of Assignment
    | FunctionDefinitionNode of FunctionDefinition
    | TypedFunctionDefinitionNode of TypedFunctionDefinition
    | FunctionCallExpression of FunctionCall
    | ObjectExpression of Object
    | AccessNode of AccessChain
    | ExpressionNode of TransformerNode list
    | ArrayLiteral of TransformerNode list
    | NoOp
    | EOF


type Delimiter =
    | Node of Parser.AST
    | DelimiterFunc of (Parser.ASTNode -> Parser.ASTNode list -> bool)
    | NoDelimiter

let raiseTransformerException (ast: Parser.ASTNode) (message: string) node =
    raise (
        TransformerException(
            ast.Line,
            ast.Column,
            message + "\n" + (JsonConvert.SerializeObject(node, Formatting.Indented))
        )
    )

let rec parseObject (isLiteral: bool) (indent: int) (remaining: Parser.ASTNode list) (children: ObjectProperty list) =
    let rec parse (isLiteral: bool) (indent: int) (remaining: Parser.ASTNode list) (children: ObjectProperty list) =
        let func = parse isLiteral indent

        match remaining with
        | [] -> (remaining, children)
        | head :: tail ->
            match (isLiteral, head.Indent < indent) with
            | false, true -> (remaining, children)
            | _ ->
                match head.Type with
                | Parser.PropertyAssignment ->
                    let (returnNodes, property) = parseAST tail []

                    match (head.Value.StartsWith("@"), property) with
                    | false, FunctionDefinitionNode x -> func returnNodes (Method(head.Value, x) :: children)
                    | true, FunctionDefinitionNode x -> func returnNodes (StaticMethod(head.Value, x) :: children)
                    | false, _ -> func returnNodes (Property(head.Value, property) :: children)
                    | true, _ -> func returnNodes (StaticProperty(head.Value, property) :: children)
                | Parser.Newline -> func tail children
                | _ -> raiseTransformerException head "Expected PropertyAssignment" (Error head.Value)

    let remaining, nodes = parse isLiteral indent remaining children
    remaining, ObjectExpression { Properties = nodes }



and parseArray (remaining: Parser.ASTNode list) (children: TransformerNode list) =
    match remaining with
    | [] -> (remaining, children)
    | head :: tail ->
        let (next, child) = parseAST tail children
        parseArray next (child :: children)

and parseFunction (delimiter: Delimiter) (remaining: Parser.ASTNode list) (children: TransformerNode list) =
    match remaining with
    | [] -> (remaining, children)
    | head :: tail ->
        match delimiter with
        | Node node when node = (head).Type -> (remaining, children)
        | DelimiterFunc func when func (head) (tail) -> (remaining, children)
        | _ -> buildTree delimiter remaining children

and parseFunctionArgs indent (remaining: Parser.ASTNode list) (children: FunctionArg list) =
    match remaining with
    | [] -> (remaining, children)
    | head :: tail ->
        match head.Type with
        | Parser.Identifier ->
            match tail with
            | next :: rest when next.Type = Parser.TypeDef ->
                parseFunctionArgs
                    indent
                    rest
                    ({ Identifier = head.Value
                       Type = Some next.Value }
                     :: children)
            | _ ->
                parseFunctionArgs
                    indent
                    tail
                    ({ Identifier = head.Value
                       Type = option.None }
                     :: children)
        | Parser.Newline
        | Parser.Comma -> parseFunctionArgs indent tail children
        | _ -> raiseTransformerException head "Expected Identifier" (Error head.Value)

and parseFunctionCall (remaining: Parser.ASTNode list) (children: TransformerNode list) =
    match remaining with
    | [] -> (remaining, children)
    | head :: tail ->
        match head.Type with
        | Parser.Identifier -> parseFunctionCall tail (Identifier head.Value :: children)
        | Parser.Number -> parseFunctionCall tail (Number head.Value :: children)
        | Parser.Comma -> parseFunctionCall tail children
        | _ -> remaining, children

and parseTypeDef (remaining: Parser.ASTNode list) (combined: string list) =
    match remaining with
    | [] -> List.rev combined |> String.concat ""
    | head :: tail -> parseTypeDef tail (head.Value :: combined)

and parseOperatorExpression (left: TransformerNode option) (remaining: Parser.ASTNode list) (children: Operation list) =
    match remaining with
    | [] -> (remaining, children)
    | head :: [] ->
        match head.Type with
        | Parser.Operator -> raiseTransformerException head "Unexpected Operator" (Error head.Value)
        | _ ->
            let remaining, child = parseAST remaining []

            remaining,
            { Left = left
              Right = child
              Operator = "" }
            :: children
    | head :: tail ->
        match head.Type with
        | Parser.Operator ->
            let r, child = parseAST tail []

            parseOperatorExpression
                None
                r
                ({ Left = left
                   Right = child
                   Operator = head.Value }
                 :: children)
        | _ -> remaining, children

and parsePropertyAccess left (remaining: Parser.ASTNode list) =
    match remaining with
    | head :: _ when head.Type = Parser.Newline -> parsePropertyAccess left remaining
    | _ :: head :: nextNode :: tail ->
        match (head.Type, nextNode.Type) with
        | Parser.Identifier, Parser.ArgumentList ->
            let _, args = parseFunctionCall nextNode.Children []

            tail,
            (MethodCall
                { Left = left
                  Name = head.Value
                  Args = args })
        | Parser.Identifier, _ -> (nextNode :: tail), PropertyAccess { Left = left; Value = head.Value }
        | _ -> raiseTransformerException head "Expected Identifier" (Error head.Value)
    | _ -> raiseTransformerException (List.head remaining) "Unexpected Token" (List.head remaining)

and parseAST
    (remaining: Parser.ASTNode list)
    (children: TransformerNode list)
    : (Parser.ASTNode list * TransformerNode) =

    match remaining with
    | [] -> (remaining, EOF)
    // | head :: next :: tail when next.Type = Parser.Operator ->
    //     let remaining, exp = parseOperatorExpression (Some(List.head children)) remaining []
    //     remaining, (OperatorExpression exp)
    | head :: tail ->

        let simplified = parseAST tail

        match head.Type with
        | Parser.EOF -> remaining, EOF
        | Parser.Root -> parseAST head.Children []
        | Parser.Comma -> (raiseTransformerException head "Unexpected comma" (Error head.Value))
        | Parser.True
        | Parser.False -> tail, (BoolExpression head.Value)
        | Parser.StringLiteral -> tail, (String head.Value)
        | Parser.Pointer ->
            match tail with
            | [] -> raiseTransformerException head "Unexpected pointer" (Error head.Value)
            | next :: rest when next.Type = Parser.Identifier ->
                parseAST rest (PointerIdentifier next.Value :: children)
            | _ -> raiseTransformerException head "Expected Identifier token" (Error head.Value)
        | Parser.PointerDeref ->
            match tail with
            | [] -> raiseTransformerException head "Unexpected Deref" (Error head.Value)
            | next :: rest when next.Type = Parser.Identifier -> parseAST rest (DeRefIdentifier next.Value :: children)
            | _ -> raiseTransformerException head "Expected Identifier token" (Error head.Value)
        | Parser.Import -> tail, Import head.Value
        | Parser.TypedArgumentList ->
            match tail with
            | [] -> raiseTransformerException head "Expected Funcdef" (Error head.Value)
            | { Type = Parser.FuncDef } :: functionElements ->
                let (delimiter, body) =
                    match functionElements with
                    | [] -> NoDelimiter, []
                    | next :: body when next.Type = Parser.Newline ->
                        (DelimiterFunc
                         <| fun x nextNodes ->
                             match x.Type with
                             | Parser.Newline ->
                                 match nextNodes with
                                 | [] -> true
                                 | next :: _ -> next.Indent <= x.Indent
                             | _ -> x.Indent <= head.Indent),
                        body
                    | _ -> (Node Parser.Newline, functionElements)

                let _, args = parseFunctionArgs head.Indent head.Children []
                let remaining, body = parseFunction delimiter body []

                remaining,
                TypedFunctionDefinitionNode
                    { Body = body
                      Args = args
                      ReturnType = head.Value }
            | _ -> raiseTransformerException head "Expected Funcdef" (Error head.Value)
        | Parser.ArgumentList ->
            match tail with
            | [] -> raiseTransformerException head "Expected Funcdef" (Error head.Value)
            | { Type = Parser.FuncDef } :: functionElements ->
                let (delimiter, body) =
                    match functionElements with
                    | [] -> NoDelimiter, []
                    | next :: body when next.Type = Parser.Newline ->
                        (DelimiterFunc
                         <| fun x nextNodes ->
                             match x.Type with
                             | Parser.Newline ->
                                 match nextNodes with
                                 | [] -> true
                                 | next :: _ -> next.Indent <= x.Indent
                             | _ -> x.Indent <= head.Indent),
                        body
                    | _ -> (Node Parser.Newline, functionElements)

                let _, args = parseFunctionArgs head.Indent head.Children []
                let remaining, body = parseFunction delimiter body []
                remaining, FunctionDefinitionNode { Body = body; Args = args }
            | _ -> raiseTransformerException head "Expected Funcdef" (Error head.Value)
        | Parser.FuncDef ->
            match tail with
            | [] -> raiseTransformerException head "Expected FuncBody" (Error head.Value)
            | nextNode :: remainingNodes ->
                match nextNode.Type with
                | Parser.Newline ->
                    let returnNodes, body =
                        parseFunction
                            (DelimiterFunc
                             <| fun x nextNodes ->
                                 match x.Type with
                                 | Parser.Newline ->
                                     match nextNodes with
                                     | [] -> true
                                     | next :: _ -> next.Indent <= x.Indent
                                 | _ -> x.Indent <= head.Indent)
                            remainingNodes
                            []

                    (returnNodes, (FunctionDefinitionNode { Args = []; Body = body }))
                | _ ->
                    let (returnNodes, body) = parseFunction (Node Parser.Newline) tail []

                    returnNodes, ((FunctionDefinitionNode { Args = []; Body = body }))
        | Parser.PropertyAssignment -> parseObject false head.Indent remaining []
        | Parser.ObjectLiteral -> parseObject true head.Indent tail []
        | Parser.Number -> tail, Number head.Value
        | Parser.Identifier -> tail, Identifier head.Value
        // match tail with
        // | [] -> simplified (Identifier head.Value :: children)
        // | nextNode :: remainingNodes ->
        //     match nextNode.Type with
        //     | Parser.Assignment ->
        //         let (returnNodes, right) = parseAST remainingNodes children

        //         returnNodes,
        //         ((AssignmentNode
        //             { Left = Identifier head.Value
        //               Right = right }))
        //     | Parser.Number
        //     | Parser.Identifier ->

        //         let (returnNodes, right) = parseFunctionCall tail []
        //         returnNodes, (FunctionCallExpression { Args = right })
        //     | Parser.ArgumentList ->
        //         let (_, children) = parseFunctionCall nextNode.Children []
        //         remainingNodes, (FunctionCallExpression { Args = children })
        //     | Parser.Comma -> parseAST remainingNodes (Identifier head.Value :: children)
        //     | Parser.TypeDef ->
        //         let t = parseTypeDef tail []
        //         remainingNodes, TypedIdentifierNode { Identifier = head.Value; Type = t }
        //     | _ -> tail, (Identifier head.Value)
        | Parser.Newline -> simplified children

and buildTree (delimiter: Delimiter) (nodes: Parser.ASTNode list) (current) =
    match nodes with
    | [] -> nodes, (EOF :: current)
    | { Type = Parser.EOF } :: _ -> nodes, current
    | _ ->
        match delimiter with
        | Node node when node = (List.head nodes).Type -> nodes, current
        | DelimiterFunc func when func (List.head nodes) (List.tail nodes) -> nodes, current
        | _ ->
            let (returnNodes, child) = parseAST nodes []

            match returnNodes with
            | x :: _ when x.Type = Parser.Operator ->
                let newNodes, right = parseOperatorExpression (Some child) returnNodes []
                buildTree delimiter newNodes ((OperatorExpression right) :: current)
            | x :: _ when x.Type = Parser.PropertyAccess ->
                let newNodes, right = parsePropertyAccess child returnNodes

                match current with
                | AccessNode l :: rest -> buildTree delimiter newNodes (AccessNode(right :: l) :: rest)
                | _ -> buildTree delimiter newNodes ((AccessNode [ right ]) :: current)
            | x :: _ when x.Type = Parser.ArgumentList ->
                let newNodes, right = parseFunctionCall returnNodes []

                match current with
                | FunctionCallExpression l :: rest ->
                    buildTree delimiter newNodes (FunctionCallExpression { Args = right } :: rest)
                | _ -> buildTree delimiter newNodes (FunctionCallExpression { Args = right } :: current)
            | x :: rest when x.Type = Parser.Assignment ->
                let newNodes, right = parseAST rest []
                buildTree delimiter newNodes (AssignmentNode { Left = child; Right = right } :: current)
            | x :: _ when x.Type = Parser.ObjectLiteral ->
                let newNodes, obj = parseObject true x.Indent returnNodes []

                match current with
                | ObjectExpression l :: rest -> buildTree delimiter newNodes (obj :: rest)
                | _ -> buildTree delimiter newNodes (obj :: current)

            | _ -> buildTree delimiter returnNodes (child :: current)

let rec reverseTransform node =
    let curriedFunc =
        List.filter (fun (x: TransformerNode) -> x <> NoOp)
        >> (List.map reverseTransform >> List.rev)

    match node with
    | RootNode { Children = children } -> RootNode { Children = curriedFunc children }
    | ExpressionNode node -> ExpressionNode <| curriedFunc node
    | OperatorExpression node -> OperatorExpression <| List.rev node
    | AssignmentNode node ->
        AssignmentNode
            { Left = reverseTransform node.Left
              Right = reverseTransform node.Right }
    | FunctionDefinitionNode node ->
        FunctionDefinitionNode
            { Args = List.rev node.Args
              Body = curriedFunc node.Body }
    | FunctionCallExpression node -> FunctionCallExpression { Args = List.rev node.Args }
    | ObjectExpression { Properties = props } ->
        List.map
            (fun x ->
                match x with
                | Property(name, value) -> Property(name, reverseTransform value)
                | Method(name, value) ->
                    Method(
                        name,
                        { Args = List.rev value.Args
                          Body = curriedFunc value.Body }
                    )
                | StaticMethod(name, value) ->
                    StaticMethod(
                        name,
                        { Args = List.rev value.Args
                          Body = curriedFunc value.Body }
                    )
                | StaticProperty(name, value) -> StaticProperty(name, reverseTransform value))
            props
        |> fun x -> ObjectExpression { Properties = List.rev x }
    | _ -> node

let transform (ast: Parser.ASTNode) =
    RootNode { Children = (buildTree NoDelimiter ast.Children []) |> snd }
    |> reverseTransform
