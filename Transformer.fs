module Transformer

open Newtonsoft.Json

exception TransformerException of int * int * string
exception ValidationError of string

type RootNode = { Children: TransformerNode list }

and Assignment =
    { Left: TransformerNode
      Right: TransformerNode }

and BoolType =
    | And
    | Or

and BoolExpression =
    { Left: TransformerNode
      Right: TransformerNode
      Operator: BoolType }

and FunctionCall =
    { Value: string
      Args: TransformerNode list }

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

and Object = ObjectProperty list

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

and AssignmentList = string list

and ObjectDestructure =
    { Left: AssignmentList
      Right: TransformerNode }

and ArrayDestructure =
    { Left: AssignmentList
      Right: TransformerNode }

and BoolLiteral =
    | True
    | False

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
    | BoolExpression of BoolExpression
    | BoolLiteral of BoolLiteral
    | ComparisonExpression of Assignment
    | AssignmentNode of Assignment
    | ArrayDestructure of ArrayDestructure
    | ObjectDestructure of ObjectDestructure
    | FunctionDefinitionNode of FunctionDefinition
    | TypedFunctionDefinitionNode of TypedFunctionDefinition
    | FunctionCallExpression of FunctionCall
    | ObjectExpression of Object
    | AccessNode of AccessChain
    | ExpressionNode of TransformerNode list
    | ArrayLiteral of TransformerNode list
    | DoExpressionNode of TransformerNode
    | NoOp
    | EOF

and FunctionCallParams =
    | Arg of TransformerNode
    | Comma

and BuildContext = TransformerNode

type Delimiter =
    | NodeDelim of Parser.AST
    | FuncDelim of (Parser.ASTNode -> Parser.ASTNode list -> TransformerNode list -> bool)
    | NoDelim

let raiseTransformerException (ast: Parser.ASTNode) (message: string) node =
    raise (
        TransformerException(
            ast.Line,
            ast.Column,
            message + "\n" + (JsonConvert.SerializeObject(node, Formatting.Indented))
        )
    )

let rec parseObject (isLiteral: bool) (remaining: Parser.ASTNode list) (children: ObjectProperty list) =
    let rec parse (isLiteral: bool) (remaining: Parser.ASTNode list) (children: ObjectProperty list) =

        match remaining with
        | [] -> (remaining, children)
        | head :: tail ->
            match head.Type with
            | Parser.PropertyAssignment ->
                let delimFunc = FuncDelim <| fun _ _ children -> (List.length children) > 0
                let (returnNodes, (property :: _)) = parseAST delimFunc tail []

                match (head.Value.StartsWith("@"), property) with
                | false, FunctionDefinitionNode x -> func returnNodes (Method(head.Value, x) :: children)
                | true, FunctionDefinitionNode x -> func returnNodes (StaticMethod(head.Value, x) :: children)
                | false, _ -> func returnNodes (Property(head.Value, property) :: children)
                | true, _ -> func returnNodes (StaticProperty(head.Value, property) :: children)
            | Parser.Newline -> func tail children
            | _ -> raiseTransformerException head "Expected PropertyAssignment" (Error head.Value)

    and func = parse isLiteral

    let remaining, nodes = func remaining children
    remaining, ObjectExpression <| nodes



and parseArray (remaining: Parser.ASTNode list) (children: TransformerNode list) =
    match remaining with
    | [] -> (remaining, children)
    | _ -> parseAST NoDelim remaining []

and parseFunction (delimiter: Delimiter) (remaining: Parser.ASTNode list) (children: TransformerNode list) =
    match remaining with
    | [] -> (remaining, children)
    | head :: tail ->
        match delimiter with
        | NodeDelim node when node = (head).Type -> (remaining, children)
        | FuncDelim func when func (head) (tail) children -> (remaining, children)
        | _ -> parseAST delimiter tail []

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
        let delimiterFunc =
            FuncDelim(fun (token: Parser.ASTNode) _ _ ->
                match head.Type with
                | Parser.Comma -> false
                | _ -> token.Indent = head.Indent)

        match head.Type with
        | Parser.Comma -> parseAST delimiterFunc tail children
        | _ -> parseAST delimiterFunc remaining children


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
            let remaining, child = parseAST NoDelim remaining []

            remaining,
            { Left = left
              Right = ExpressionNode child
              Operator = "" }
            :: children
    | head :: tail ->
        match head.Type with
        | Parser.Operator ->
            let r, child = parseAST NoDelim tail []

            parseOperatorExpression
                None
                r
                ({ Left = left
                   Right = ExpressionNode child
                   Operator = head.Value }
                 :: children)
        | Parser.Newline ->
            match children with
            // | Operator _ -> parseOperatorExpression left tail children
            | _ -> remaining, children
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

and parseAssignment (remaining: Parser.ASTNode list) children =

    match remaining with
    | [] -> (remaining, children)
    | head :: _ ->
        let delim = FuncDelim <| fun token _ _ -> token.Indent <= head.Indent
        parseAST delim remaining children

and parseBoolExpression delimiter head tail children type' =
    match children with
    | previousChild :: rest ->

        let remainingNodes, right = parseAST delimiter tail []

        remainingNodes,
        (BoolExpression
            { Left = previousChild
              Right = ExpressionNode right
              Operator = type' }
         :: rest)

    | _ -> raiseTransformerException head "Expected previous child" (Error head.Value)


and parseAST
    (delimiter: Delimiter)
    (remaining: Parser.ASTNode list)
    (children: TransformerNode list)
    : (Parser.ASTNode list * TransformerNode List) =

    match remaining with
    | [] -> (remaining, children)
    | head :: tail ->
        match delimiter with
        | NodeDelim node when node = head.Type -> (remaining, children)
        | FuncDelim f when (f head tail children) -> (remaining, children)
        | _ ->
            match head.Type with
            | Parser.EOF -> tail, EOF :: children
            | Parser.Root -> parseAST NoDelim head.Children []
            | Parser.ObjectLiteral ->
                let newNodes, newChildren = parseObject true head.Children []
                parseAST NoDelim newNodes (newChildren :: children)
            | Parser.ArrayLiteral ->
                let newNodes, newChildren = parseArray head.Children []
                parseAST NoDelim newNodes (ArrayLiteral newChildren :: children)
            | Parser.ParenExpression
            | Parser.IndentedBlock -> parseAST NoDelim head.Children []
            | Parser.And -> parseBoolExpression delimiter head tail children And ||> parseAST delimiter
            | Parser.Or -> parseBoolExpression delimiter head tail children Or ||> parseAST delimiter
            | Parser.True -> parseAST delimiter tail (BoolLiteral True :: children)
            | Parser.False -> parseAST delimiter tail (BoolLiteral False :: children)
            | Parser.ArrayDestructure ->
                let left = List.map (fun (x: Parser.ASTNode) -> x.Value) head.Children
                let remainingNodes, right = parseAssignment tail []

                parseAST
                    delimiter
                    remainingNodes
                    ((ArrayDestructure
                        { Left = left
                          Right = ExpressionNode right })
                     :: children)
            | Parser.ObjectDestructure ->
                let left = List.map (fun (x: Parser.ASTNode) -> x.Value) head.Children
                let remainingNodes, right = parseAssignment tail []

                parseAST
                    delimiter
                    remainingNodes
                    ((ObjectDestructure
                        { Left = left
                          Right = ExpressionNode right })
                     :: children)
            | Parser.ArgumentList ->
                match tail with
                | first :: second :: third :: remainder when
                    first.Type = Parser.FuncDef
                    && second.Type = Parser.Newline
                    && third.Type = Parser.IndentedBlock
                    ->
                    let _, args = parseFunctionArgs head.Indent head.Children []
                    let remaining, body = parseFunction (NodeDelim Parser.Newline) remainder []

                    (remaining, (FunctionDefinitionNode { Args = args; Body = body } :: children))
                    ||> parseAST delimiter
                | _ -> raiseTransformerException head "Expected Funcdef" (Error head.Value)
            | Parser.Identifier ->
                match tail with
                | x :: _ when x.Type = Parser.AST.ArgumentList || x.Type = Parser.AST.TypedArgumentList ->
                    let newNodes, newChildren = parseFunctionCall x.Children [] in

                    (newNodes,
                     (FunctionCallExpression
                         { Value = head.Value
                           Args = newChildren }
                      :: children))
                    ||> parseAST delimiter
                | x :: rest when x.Type = Parser.Operator ->
                    let newNodes, right = parseOperatorExpression (Some(Identifier head.Value)) rest []

                    parseAST delimiter newNodes (OperatorExpression right :: children)
                | x :: rest when x.Type = Parser.Assignment ->
                    let newNodes, right = parseAssignment rest []

                    parseAST
                        delimiter
                        newNodes
                        (AssignmentNode
                            { Left = Identifier head.Value
                              Right = ExpressionNode right }
                         :: children)
                | _ -> parseAST delimiter tail ((Identifier head.Value) :: children)


and buildTree (currentIndent: int) (nodes: Parser.ASTNode list) (current: TransformerNode list) =
    match nodes with
    | [] -> nodes, current
    | { Type = Parser.EOF } :: _ -> nodes, current
    | _ ->
        let remaining, children = parseAST NoDelim nodes []
        buildTree currentIndent remaining (List.concat [ children; current ])

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
    | FunctionCallExpression node ->
        FunctionCallExpression
            { Value = node.Value
              Args = List.rev node.Args }
    | ObjectExpression props ->
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
        |> fun x -> ObjectExpression <| List.rev x
    | DoExpressionNode node -> DoExpressionNode <| reverseTransform node
    | _ -> node

let transform (ast: Parser.ASTNode) =
    RootNode { Children = (buildTree 0 ast.Children []) |> snd }
    |> fun ast ->
        match ast with
        | RootNode x -> RootNode { Children = EOF :: x.Children }
        | _ -> ast
    |> reverseTransform
