module Parser

type AST =
    | Root // Root node
    | Import // e.g. import "module"
    | Identifier // e.g. x
    | Number // e.g. 1
    | FuncDef // Function definition e.g. ->
    | Expression // e.g. x + y
    | ParenExpression // e.g. (x + y)
    | TypedParenExpression // e.g. (x + y)::int
    | Object // Object literal without braces
    | ArrayLiteral // e.g. [1, 2, 3]
    | ObjectLiteral // e.g. { x: 1, y: 2 }
    | StringLiteral // e.g. "hello"
    | ArrayDestructure // Destructuring e.g. let [x, y] = arr
    | ObjectDestructure // Destructuring e.g. let { x, y } = obj
    | ArgumentList // Function arguments e.g. (x, y) ->
    | TypedArgumentList // e.g. (x,y)::int ->
    | Comma // ,
    | PropertyAssignment // : operator
    | Assignment // = operator
    | PropertyAccess // . operator
    | IndexAccess // x[x]
    | FunctionCall // e.g. f(x, y) or f x, y
    | IfExpression // e.g. if x > 0
    | ElseExpression // e.g. else
    | ThenExpression // e.g. then
    | Operator // e.g. +, -, *, /
    | TypeDef // e.g. ::int
    | Continue // Continue statement
    | Break // Break statement
    | Return // Return statement
    | For // For loop
    | While // While loop
    | DoExpression // Do expression, e.g. do func
    | RangeExpression // e.g. 1..10
    | StructDefinition // e.g. struct Point OR class Point
    | Extends
    | IncrementExpression
    | DecrementExpression
    | MemberAccess
    | This
    | And
    | Or
    | True
    | False
    | Newline
    | Pointer
    | PointerDeref
    | IndentedBlock
    | EOF



type ASTNode =
    { Type: AST
      Value: string
      Children: ASTNode list
      Line: int
      Column: int
      Indent: int }

type Delimiter =
    | Func of (int -> Lexer.TokenType -> Lexer.TokenType list -> ASTNode -> bool)
    | NoDelimiter

exception ParseException of (Lexer.Token * int * int * string)

let raiseParseError msg ast (token: Option<Lexer.Token>) =
    match token with
    | Some x ->
        raise (
            ParseException(
                x,
                ast.Line,
                ast.Column,
                sprintf "Parse error: %s at line %d column %d" msg ast.Line ast.Column
            )
        )
    | None ->
        raise (
            ParseException(
                { Value = ""
                  Line = ast.Line
                  Column = ast.Column },
                ast.Line,
                ast.Column,
                sprintf "Parse error: %s at line %d column %d" msg ast.Line ast.Column
            )
        )

let mapTokenToNode indent (token: Lexer.Token) nodeType =
    { Type = nodeType
      Value = token.Value
      Children = []
      Line = token.Line
      Column = token.Column
      Indent = indent }

let checkClosing token rest ast =
    match token with
    | Lexer.RParen x ->
        match ast.Type with
        | ParenExpression
        | TypedArgumentList
        | ArgumentList -> (rest, ast)
        | _ -> raiseParseError "Unexpected closing parenthesis" ast (Some x)
    | Lexer.RBrace x ->
        match ast.Type with
        | ObjectLiteral
        | ObjectDestructure -> (rest, ast)
        | _ -> raiseParseError "Unexpected closing brace" ast (Some x)
    | Lexer.RBracket x ->
        match ast.Type with
        | ArrayLiteral
        | ArrayDestructure
        | IndexAccess -> (rest, ast)
        | _ -> raiseParseError "Unexpected closing bracket" ast (Some x)
    | _ -> raiseParseError "Unexpected closing token" ast None

let rec ignoreWhitespace ignoreNewLines tokens =
    match tokens with
    | [] -> []
    | head :: rest ->
        match head with
        | Lexer.Whitespace _ -> ignoreWhitespace ignoreNewLines rest
        | Lexer.NewLine _ ->
            if ignoreNewLines then
                ignoreWhitespace ignoreNewLines rest
            else
                tokens
        | _ -> tokens

let getNextIgnoreWhitespace ignoreNewLines tokens =
    ignoreWhitespace ignoreNewLines tokens |> List.head

let rec handleNewLine indent tokens ast =
    match tokens with
    | [] -> (indent, [])
    | head :: rest ->
        match ast.Type with
        | ObjectLiteral
        | ObjectDestructure
        | ArrayLiteral
        | ArrayDestructure -> (indent, tokens)
        | _ ->
            match head with
            | Lexer.Whitespace _
            | Lexer.Tab _ -> handleNewLine (indent + 1) rest ast
            | _ -> (indent, tokens)

let checkASTIsLiteral ast =
    match ast.Type with
    | ArrayLiteral
    | ObjectLiteral -> true
    | _ -> false

let rec handleComment tokens =
    match tokens with
    | [] -> []
    | head :: rest ->
        match head with
        | Lexer.NewLine _ -> tokens
        | _ -> handleComment rest

let recursiveParseFunc currentIndent rest ast f (token: Lexer.Token) t =
    let t, a = f currentIndent rest (mapTokenToNode currentIndent token t)

    f
        currentIndent
        t
        { ast with
            Children = a :: ast.Children }

let rec parseTypeFunc
    (mapFunc: Lexer.Token -> AST -> ASTNode)
    (t: Lexer.TokenType list)
    (current: ASTNode list)
    (ast: ASTNode)
    =
    match t with
    | Lexer.Identifier head :: rest -> parseTypeFunc mapFunc rest (mapFunc head Identifier :: current) ast
    | Lexer.Period head :: rest -> parseTypeFunc mapFunc rest (mapFunc head MemberAccess :: current) ast
    | Lexer.Pointer head :: rest -> parseTypeFunc mapFunc rest (mapFunc head Pointer :: current) ast
    | Lexer.PointerDeref head :: rest -> parseTypeFunc mapFunc rest (mapFunc head PointerDeref :: current) ast
    | Lexer.Comma _ :: _ -> t, current
    | Lexer.RParen _ :: _ -> t, current
    | Lexer.Whitespace _ :: rest -> rest, current
    | _ -> raiseParseError "Expected type" ast None

let rec parseTree (delimiter: Delimiter) currentIndent tokens ast =
    let mapFunc = mapTokenToNode currentIndent
    let parse = parseTree delimiter

    match currentIndent < ast.Indent with
    | true -> (tokens, ast)
    | _ ->
        match tokens with
        | [] -> ([], ast)
        | head :: rest ->


            match delimiter with
            | Func f when f currentIndent head rest ast -> tokens, ast
            | _ ->
                let curriedRecursiveParseFunc =
                    recursiveParseFunc currentIndent rest ast (parseTree delimiter)

                let curriedParseFunc t (token: Lexer.Token) =
                    parse
                        currentIndent
                        rest
                        { ast with
                            Children = (mapFunc token t) :: ast.Children }

                match head with
                | Lexer.Error x -> raise (ParseException(x, ast.Line, ast.Column, "Unexpected error token"))
                | Lexer.EOF x ->
                    ([],
                     { ast with
                         Children =
                             ({ Type = EOF
                                Children = []
                                Line = x.Line
                                Value = "EOF"
                                Column = x.Column
                                Indent = currentIndent }
                              :: ast.Children) })
                | Lexer.Import x ->
                    match rest with
                    | Lexer.String token :: restOfTokens ->
                        parse
                            currentIndent
                            restOfTokens
                            { ast with
                                Children = mapFunc token Import :: ast.Children }
                    | _ -> raise (ParseException(x, x.Line, x.Column, "Expected string literal"))
                | Lexer.NewLine x ->
                    let i, t = handleNewLine 0 rest ast

                    match (i > currentIndent) with
                    | true ->
                        let t, a =
                            parse
                                i
                                t
                                { Type = IndentedBlock
                                  Value = ""
                                  Children = []
                                  Line = x.Line
                                  Column = x.Column
                                  Indent = i }

                        parse
                            currentIndent
                            t
                            { ast with
                                Children = a :: ast.Children }
                    | false ->
                        parse
                            i
                            t
                            { ast with
                                Children =
                                    { Type = Newline
                                      Value = ""
                                      Children = []
                                      Line = x.Line
                                      Column = x.Column
                                      Indent = currentIndent }
                                    :: ast.Children }
                | Lexer.Whitespace _
                | Lexer.Tab _ -> parse currentIndent rest ast
                | Lexer.Hash _ ->
                    let tokens = handleComment rest
                    parse currentIndent tokens ast
                | Lexer.Period x -> curriedParseFunc MemberAccess x
                | Lexer.Identifier token ->
                    match rest with
                    | [] -> raiseParseError "Expected token" ast (Some token)
                    | nextToken :: restOfTokens ->
                        match nextToken with
                        | Lexer.LParen _ ->
                            let t, a = parse currentIndent restOfTokens (mapFunc token FunctionCall)

                            parse
                                currentIndent
                                t
                                { ast with
                                    Children = a :: ast.Children }
                        | Lexer.Colon _ ->
                            parse
                                currentIndent
                                restOfTokens
                                { ast with
                                    Children = (mapFunc token PropertyAssignment :: ast.Children) }
                        | _ ->
                            parse
                                currentIndent
                                rest
                                { ast with
                                    Children =
                                        { Type = Identifier
                                          Value = token.Value
                                          Children = []
                                          Line = token.Line
                                          Column = token.Column
                                          Indent = currentIndent }
                                        :: ast.Children }
                | Lexer.Number token -> curriedParseFunc Number token
                | Lexer.LParen token ->
                    let t, a = parse currentIndent rest (mapFunc token ParenExpression)

                    match List.head <| ignoreWhitespace false t with
                    | Lexer.FuncDef _ ->
                        parse
                            currentIndent
                            t
                            { ast with
                                Children = { a with Type = ArgumentList } :: ast.Children }
                    | Lexer.DoubleColon _ ->

                        let t, returnType = parseTypeFunc mapFunc (List.tail t) [] ast

                        match ignoreWhitespace false t with
                        | Lexer.FuncDef _ :: _ ->
                            parse
                                currentIndent
                                t
                                { ast with
                                    Children =
                                        { a with
                                            Type = TypedArgumentList
                                            Value =
                                                List.rev returnType |> List.map (fun x -> x.Value) |> String.concat "" }
                                        :: ast.Children }
                        | _ -> raiseParseError "Expected function definition" ast None
                    | _ ->
                        parse
                            currentIndent
                            t
                            { ast with
                                Children = a :: ast.Children }
                | Lexer.RParen _ -> checkClosing head rest ast
                | Lexer.LBracket token -> curriedRecursiveParseFunc token ArrayLiteral
                | Lexer.RBracket _ -> checkClosing head rest ast
                | Lexer.LBrace token -> curriedRecursiveParseFunc token ObjectLiteral
                | Lexer.RBrace _ -> checkClosing head rest ast
                | Lexer.FuncDef token ->
                    match rest with
                    | [] -> raise (ParseException(token, token.Line, token.Column, "Expected function body"))
                    | _ -> curriedParseFunc FuncDef token
                | Lexer.Comma x ->
                    match ast.Type with
                    | TypeDef -> rest, ast
                    | ArgumentList
                    | TypedArgumentList
                    | Object
                    | ObjectLiteral
                    | ObjectDestructure
                    | ArrayLiteral
                    | ParenExpression
                    | ArrayDestructure -> parse currentIndent rest ast
                    | _ -> raiseParseError "Unexpected comma" ast (Some x)
                | Lexer.If x -> curriedParseFunc IfExpression x
                | Lexer.Else x -> curriedParseFunc ElseExpression x
                | Lexer.Then x -> curriedParseFunc ThenExpression x
                | Lexer.String token -> curriedParseFunc StringLiteral token
                | Lexer.Operator token -> curriedParseFunc Operator token
                | Lexer.DoubleColon token ->
                    let t, returnType = parseTypeFunc mapFunc rest [] ast

                    parse
                        currentIndent
                        t
                        { ast with
                            Children =
                                { Type = TypeDef
                                  Value = token.Value
                                  Children = returnType
                                  Line = token.Line
                                  Column = token.Column
                                  Indent = currentIndent }
                                :: ast.Children }

                | Lexer.Continue token -> curriedParseFunc Continue token
                | Lexer.Return token -> curriedParseFunc Return token
                | Lexer.Break token -> curriedParseFunc Break token
                | Lexer.Switch x -> // TODO implement switch
                    raiseParseError "Switch statement not implemented" ast (Some x)
                | Lexer.Assign x -> curriedParseFunc Assignment x
                | Lexer.For x -> curriedParseFunc For x
                | Lexer.While x -> curriedParseFunc While x
                | Lexer.Do x -> curriedParseFunc DoExpression x
                | Lexer.DoublePeriod x -> curriedParseFunc RangeExpression x
                | Lexer.Pointer x ->
                    match rest with
                    | Lexer.Whitespace _ :: restOfTokens ->
                        parse
                            currentIndent
                            restOfTokens
                            { ast with
                                Children =
                                    { Type = Operator
                                      Value = x.Value
                                      Children = []
                                      Line = x.Line
                                      Column = x.Column
                                      Indent = currentIndent }
                                    :: ast.Children }
                    | _ ->
                        parse
                            currentIndent
                            rest
                            { ast with
                                Children =
                                    { Type = Pointer
                                      Value = x.Value
                                      Children = []
                                      Line = x.Line
                                      Column = x.Column
                                      Indent = currentIndent }
                                    :: ast.Children }
                | Lexer.PointerDeref x ->
                    match rest with
                    | Lexer.Whitespace _ :: restOfTokens ->
                        parse
                            currentIndent
                            restOfTokens
                            { ast with
                                Children =
                                    { Type = Operator
                                      Value = x.Value
                                      Children = []
                                      Line = x.Line
                                      Column = x.Column
                                      Indent = currentIndent }
                                    :: ast.Children }
                    | _ ->
                        parse
                            currentIndent
                            rest
                            { ast with
                                Children =
                                    { Type = PointerDeref
                                      Value = x.Value
                                      Children = []
                                      Line = x.Line
                                      Column = x.Column
                                      Indent = currentIndent }
                                    :: ast.Children }
                | Lexer.Struct x ->
                    match rest with
                    | Lexer.Identifier token :: restOfTokens ->
                        parse
                            currentIndent
                            restOfTokens
                            { Type = StructDefinition
                              Value = token.Value
                              Children = []
                              Line = token.Line
                              Column = token.Column
                              Indent = currentIndent }
                    | _ -> raiseParseError "Expected identifier" ast None
                | Lexer.Extends x ->
                    match rest with
                    | Lexer.Identifier token :: restOfTokens ->
                        parse
                            currentIndent
                            restOfTokens
                            { Type = Extends
                              Value = token.Value
                              Children = []
                              Line = token.Line
                              Column = token.Column
                              Indent = currentIndent }
                    | _ -> raiseParseError "Extends token expects Identifier" ast None
                | Lexer.Increment x -> curriedParseFunc IncrementExpression x
                | Lexer.Decrement x -> curriedParseFunc DecrementExpression x
                | Lexer.MemberAccess x ->
                    match rest with
                    | Lexer.Identifier token :: restOfTokens ->
                        parse
                            currentIndent
                            restOfTokens
                            { ast with
                                Children =
                                    { Type = MemberAccess
                                      Value = "this"
                                      Children = []
                                      Line = token.Line
                                      Column = token.Column
                                      Indent = currentIndent }
                                    :: ast.Children }
                    | _ ->
                        parse
                            currentIndent
                            rest
                            { Type = This
                              Value = "this"
                              Children = []
                              Line = x.Line
                              Column = x.Column
                              Indent = currentIndent }
                | Lexer.And x -> curriedParseFunc And x
                | Lexer.Or x -> curriedParseFunc Or x
                | Lexer.True x -> curriedParseFunc True x
                | Lexer.False x -> curriedParseFunc False x
                | _ -> raiseParseError "Unexpected token" ast None

let rec reverseChildren ast =
    { ast with
        Children = List.rev ast.Children |> List.map reverseChildren }

let rec recursiveParse tokens (ast: ASTNode) =
    match tokens with
    | [] -> (tokens, ast)
    | _ ->
        let t, a = parseTree NoDelimiter 0 tokens ast

        recursiveParse t a


let parse tokens =
    recursiveParse
        tokens
        { Type = Root
          Value = ""
          Line = 0
          Column = 0
          Children = []
          Indent = 0 }
    |> snd
    |> reverseChildren
