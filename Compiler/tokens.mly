%token <int> CInt
%token <string> Ident
%token <string> StringLiteral
%token Anonymous Assembly Break Const Continue Contract Default Delete Do Else Enum Event External
%token False For Function If In Indexed Internal Import Is Library Mapping Memory Modifier New Null
%token Public Private Return Returns Storage Struct Throw True Var While Underscore
%token SubWei SubSzabo SubFinney SubEther SubSeconds SubMinute SubHour SubDays SubWeek SubYear After
%token Int UInt Bytes Byte String Address Bool Fixed UFixed
%token Lt Le Gt Ge Assign Equal Arrow Not NotEqual Plus Inc AssignAdd Minus Dec AssignSub Mul AssignMul
%token And Or Period Colon Semicolon Comma LParen RParen LBrack RBrack LBrace RBrace Conditional EOF Atmark

/* Associativity */
%nonassoc If
%nonassoc Else
%nonassoc Conditional
%nonassoc Not
%left Or
%left And
%left Equal NotEqual
%left Lt Le Gt Ge
%left Plus Minus
%left Mul
%right Inc Dec
%left Period
%%
