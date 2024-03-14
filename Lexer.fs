module Lexer

open System

type Token =
    { Line: int
      Column: int
      Value: string }

type TokenType =
    | Import of Token
    | Identifier of Token
    | Let of Token
    | Go of Token
    | Do of Token
    | Switch of Token
    | If of Token
    | Then of Token
    | Else of Token
    | True of Token
    | False of Token
    | And of Token
    | Or of Token
    | For of Token
    | While of Token
    | Break of Token
    | Continue of Token
    | Return of Token
    | Struct of Token
    | Extends of Token
    | MemberAccess of Token
    | FuncDef of Token
    | Channel of Token
    | Number of Token
    | String of Token
    | Operator of Token
    | Pointer of Token
    | PointerDeref of Token
    | Assign of Token
    | Comparison of Token
    | Increment of Token
    | Decrement of Token
    | Colon of Token
    | DoubleColon of Token
    | Period of Token
    | DoublePeriod of Token
    | Comma of Token
    | Hash of Token
    | LParen of Token
    | RParen of Token
    | LBrace of Token
    | RBrace of Token
    | LBracket of Token
    | RBracket of Token
    | Whitespace of Token
    | Tab of Token
    | NewLine of Token
    | EOF of Token
    | Error of Token

type LexerState =
    { LineState: int
      ColumnState: int
      Tokens: TokenType list
      Current: char list
      IsNewLine: bool }

exception LexerException of (int * int * string)

let checkNumber (chars: char list) =
    match chars with
    | [] -> false
    | head :: tail ->
        if (not << System.Char.IsDigit) head then
            false
        else
            List.forall (fun x -> System.Char.IsDigit x || x = '_') tail

let parseCurrent acc =

    let filtered = List.filter (System.Char.IsWhiteSpace >> not) acc.Current

    match filtered with
    | [] -> acc
    | _ ->
        let value = new string (List.toArray filtered)

        let t =
            if checkNumber filtered then
                Number
            else
                match value with
                | "if" -> If
                | "then" -> Then
                | "else" -> Else
                | "let" -> Let
                | "true" -> True
                | "false" -> False
                | "and" -> And
                | "or" -> Or
                | "go" -> Go
                | "switch" -> Switch
                | "import" -> Import
                | "class"
                | "struct" -> Struct
                | "extends" -> Extends
                | "return" -> Return
                | "for" -> For
                | "while" -> While
                | "break" -> Break
                | "continue" -> Continue
                | "do" -> Do
                | _ -> Identifier

        { acc with
            Tokens =
                t (
                    { Line = acc.LineState
                      Column = acc.ColumnState
                      Value = value }
                )
                :: acc.Tokens
            ColumnState = acc.ColumnState + (List.length filtered)
            Current = []
            IsNewLine = false }

let checkWhitespace acc a =

    // Check if the first element of the "current" list is a double quote
    // If it is then we are inside a string
    let isString =
        match acc.Current with
        | [] -> false
        | head :: _ -> head = '"'

    let parseFunc = if isString then id else parseCurrent

    let tokenFunc =
        fun (thisAcc) (token) ->
            match isString with
            | true -> thisAcc.Tokens
            | false -> token :: thisAcc.Tokens

    let appendCurrentFunc =
        fun thisAcc ->
            match isString with
            | true -> List.append thisAcc.Current [ a ]
            | false -> thisAcc.Current

    let newAcc: LexerState = parseFunc acc

    match a, isString with
    | ('\n', false)
    | ('\r', false) ->
        { newAcc with
            Tokens =
                tokenFunc
                    newAcc
                    (NewLine
                        { Line = newAcc.LineState
                          Column = newAcc.ColumnState
                          Value = Char.ToString a })
            Current = appendCurrentFunc newAcc
            LineState = newAcc.LineState + 1
            ColumnState = 1
            IsNewLine = true }
    | (' ', false) ->
        match (newAcc.IsNewLine) with
        | false ->
            { newAcc with
                Tokens =
                    tokenFunc
                        newAcc
                        (Whitespace
                            { Line = newAcc.LineState
                              Column = newAcc.ColumnState
                              Value = " " })
                Current = appendCurrentFunc newAcc }
        | true ->
            match (newAcc.Tokens) with
            | [] ->
                { newAcc with
                    Tokens =
                        tokenFunc
                            newAcc
                            (Whitespace
                                { Line = newAcc.LineState
                                  Column = newAcc.ColumnState
                                  Value = " " })
                    Current = appendCurrentFunc newAcc
                    ColumnState = newAcc.ColumnState + 1 }
            | previousChar :: _ ->
                match previousChar with
                | Tab _ -> raise (LexerException(newAcc.LineState, newAcc.ColumnState, "Can't mix tabs and spaces"))
                | _ ->
                    { newAcc with
                        Tokens =
                            tokenFunc
                                newAcc
                                (Whitespace
                                    { Line = newAcc.LineState
                                      Column = newAcc.ColumnState
                                      Value = " " })
                        Current = appendCurrentFunc newAcc
                        ColumnState = newAcc.ColumnState + 1 }
    | ('\t', false) ->
        match (newAcc.IsNewLine) with
        | false -> newAcc
        | true ->
            match newAcc.Tokens with
            | [] ->
                { newAcc with
                    Tokens =
                        tokenFunc
                            newAcc
                            (Tab
                                { Line = newAcc.LineState
                                  Column = newAcc.ColumnState
                                  Value = "\t" })
                    Current = appendCurrentFunc newAcc
                    ColumnState = newAcc.ColumnState + 4 }
            | previousChar :: _ ->
                match previousChar with
                | Whitespace _ ->
                    raise (LexerException(newAcc.LineState, newAcc.ColumnState, "Can't mix tabs and spaces"))
                | _ ->
                    { newAcc with
                        Tokens =
                            (tokenFunc
                                newAcc
                                (Tab
                                    { Line = newAcc.LineState
                                      Column = newAcc.ColumnState
                                      Value = "\t" }))
                        Current = appendCurrentFunc newAcc
                        ColumnState = newAcc.ColumnState + 4 }
    | _ ->
        { acc with
            Current = List.append acc.Current [ a ]
            IsNewLine = false }

type CharFuncInput =
    | Token of (Token -> TokenType)
    | Char
    | Ignore of LexerState

let charToken acc a tokenType =
    match tokenType with
    | Token t ->
        { acc with
            Tokens =
                t
                    { Line = acc.LineState
                      Column = acc.ColumnState
                      Value = Char.ToString a }
                :: acc.Tokens
            ColumnState = acc.ColumnState + 1
            Current = []
            IsNewLine = false }
    | Char ->
        { acc with
            Current = List.append acc.Current [ a ]
            IsNewLine = false }
    | Ignore result -> result

let matchChar currentAcc a =
    let acc = parseCurrent currentAcc

    charToken
        acc
        a
        (match a with
         | '*' -> Token PointerDeref
         | '&' -> Token Pointer
         | '/'
         | '%'
         | '!'
         | '|'
         | '^'
         | '~' -> Token Operator
         | ',' -> Token Comma
         | '#' -> Token Hash
         | '(' -> Token LParen
         | ')' -> Token RParen
         | '{' -> Token LBrace
         | '}' -> Token RBrace
         | '[' -> Token LBracket
         | ']' -> Token RBracket
         | '@' -> Token MemberAccess
         | ':'
         | '.'
         | '+' -> Char
         | _ -> Ignore <| checkWhitespace currentAcc a)

let checkSpecialChars a =
    not (
        (Char.IsLetterOrDigit a)
        || (Char.IsWhiteSpace a)
        || (Char.IsPunctuation a)
        || Char.IsSymbol a
    )

let parseText (acc: LexerState) (a: char) =
    // Do a little filtering first for characters we're not interested in
    // Not sure why these appear but if anything pops up in the output that doesn't make sense
    // then it probably should be added here
    match checkSpecialChars a with
    | true -> acc
    | false ->

        // First check the current character and then match it to the appropriate token
        match acc.Current with
        | '"' :: _ ->
            match a with
            | '"' ->
                { acc with
                    Tokens =
                        String
                            { Line = acc.LineState
                              Column = acc.ColumnState
                              Value = new string (List.tail acc.Current |> List.toArray) }
                        :: acc.Tokens
                    ColumnState = acc.ColumnState + 1
                    Current = [] }
            | _ -> checkWhitespace acc a
        | '\'' :: _ ->
            match a with
            | '\'' ->
                { acc with
                    Tokens =
                        String
                            { Line = acc.LineState
                              Column = acc.ColumnState
                              Value = new string (List.tail acc.Current |> List.toArray) }
                        :: acc.Tokens
                    ColumnState = acc.ColumnState + 1
                    Current = [] }
            | _ -> checkWhitespace acc a
        | ':' :: _ ->
            match a with
            | ':' ->
                { acc with
                    Tokens =
                        DoubleColon
                            { Line = acc.LineState
                              Column = acc.ColumnState
                              Value = "::" }
                        :: acc.Tokens
                    ColumnState = acc.ColumnState + 2
                    Current = [] }
            | _ ->
                let newAcc =
                    { acc with
                        Tokens =
                            Colon
                                { Line = acc.LineState
                                  Column = acc.ColumnState
                                  Value = ":" }
                            :: acc.Tokens
                        ColumnState = acc.ColumnState + 1
                        Current = [] }

                matchChar newAcc a
        | '.' :: _ ->
            match a with
            | '.' ->
                { acc with
                    Tokens =
                        DoublePeriod
                            { Line = acc.LineState
                              Column = acc.ColumnState
                              Value = ".." }
                        :: acc.Tokens
                    ColumnState = acc.ColumnState + 2
                    Current = [] }
            | _ ->
                let newAcc =
                    { acc with
                        Tokens =
                            Period
                                { Line = acc.LineState
                                  Column = acc.ColumnState
                                  Value = "." }
                            :: acc.Tokens
                        ColumnState = acc.ColumnState + 1
                        Current = [] }

                matchChar newAcc a
        | '+' :: _ ->
            match a with
            | '+' ->
                { acc with
                    Tokens =
                        Increment
                            { Line = acc.LineState
                              Column = acc.ColumnState
                              Value = "++" }
                        :: acc.Tokens
                    ColumnState = acc.ColumnState + 2
                    Current = [] }
            | _ ->
                let newAcc =
                    { acc with
                        Tokens =
                            Operator
                                { Line = acc.LineState
                                  Column = acc.ColumnState
                                  Value = "+" }
                            :: acc.Tokens
                        ColumnState = acc.ColumnState + 1
                        Current = [] }

                matchChar newAcc a
        | '-' :: _ ->
            match a with
            | '>' ->
                { acc with
                    Tokens =
                        FuncDef
                            { Line = acc.LineState
                              Column = acc.ColumnState
                              Value = "->" }
                        :: acc.Tokens
                    ColumnState = acc.ColumnState + 2
                    Current = [] }
            | '-' ->
                { acc with
                    Tokens =
                        Decrement
                            { Line = acc.LineState
                              Column = acc.ColumnState
                              Value = "--" }
                        :: acc.Tokens
                    ColumnState = acc.ColumnState + 2
                    Current = [] }
            | _ ->
                let newAcc =
                    { acc with
                        Tokens =
                            Operator
                                { Line = acc.LineState
                                  Column = acc.ColumnState
                                  Value = "-" }
                            :: acc.Tokens
                        ColumnState = acc.ColumnState + 1
                        Current = [] }

                matchChar newAcc a
        | '<' :: _ ->
            match a with
            | '-' ->
                { acc with
                    Tokens =
                        Channel
                            { Line = acc.LineState
                              Column = acc.ColumnState
                              Value = "<-" }
                        :: acc.Tokens
                    ColumnState = acc.ColumnState + 2
                    Current = [] }
            | _ ->
                let newAcc =
                    { acc with
                        Tokens =
                            Operator
                                { Line = acc.LineState
                                  Column = acc.ColumnState
                                  Value = "<" }
                            :: acc.Tokens
                        ColumnState = acc.ColumnState + 1
                        Current = [] }

                matchChar newAcc a
        | '=' :: _ ->
            match a with
            | '=' ->
                { acc with
                    Tokens =
                        Comparison
                            { Line = acc.LineState
                              Column = acc.ColumnState
                              Value = "==" }
                        :: acc.Tokens
                    ColumnState = acc.ColumnState + 2
                    Current = [] }
            | _ ->
                let newAcc =
                    { acc with
                        Tokens =
                            Assign
                                { Line = acc.LineState
                                  Column = acc.ColumnState
                                  Value = "=" }
                            :: acc.Tokens
                        ColumnState = acc.ColumnState + 1
                        Current = [] }

                matchChar newAcc a
        | _ -> matchChar acc a


let lex (filePath: string) =
    let fileText = System.IO.File.ReadAllText(filePath)

    let state =
        { LineState = 1
          ColumnState = 1
          Tokens = []
          Current = []
          IsNewLine = true }

    List.fold parseText state (List.ofSeq fileText)
    |> fun x -> EOF { Line = 0; Column = 0; Value = "EOF" } :: x.Tokens
    |> List.rev
