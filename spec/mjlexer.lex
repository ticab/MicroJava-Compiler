
package rs.ac.bg.etf.pp1;

import java_cup.runtime.Symbol;

%%

%{

	private Symbol new_symbol(int type) {
		return new Symbol(type, yyline+1, yycolumn);
	}
	
	private Symbol new_symbol(int type, Object value) {
		return new Symbol(type, yyline+1, yycolumn, value);
	}

%}

%cup
%line
%column

%xstate COMMENT

%eofval{
	return new_symbol(sym.EOF);
%eofval}

%%

// White characters
" " 	{ }
"\b" 	{ }
"\t" 	{ }
"\r\n" 	{ }
"\f" 	{ }

// Keywords

"program"   { return new_symbol(sym.PROG, yytext()); }
"namespace"   { return new_symbol(sym.NAMESPACE, yytext()); }
"break"  	{ return new_symbol(sym.BREAK, yytext()); }
"else"  	{ return new_symbol(sym.ELSE, yytext()); }
"const"		{ return new_symbol(sym.CONST, yytext()); }
"if"		{ return new_symbol(sym.IF, yytext()); }
"for"		{ return new_symbol(sym.FOR, yytext()); }
"new" 		{ return new_symbol(sym.NEW, yytext()); }
"print" 	{ return new_symbol(sym.PRINT, yytext()); }
"read" 		{ return new_symbol(sym.READ, yytext()); }
"return" 	{ return new_symbol(sym.RETURN, yytext()); }
"void" 		{ return new_symbol(sym.VOID, yytext()); }
"continue" 	{ return new_symbol(sym.CONTINUE, yytext()); }
'.'		 	{ return new_symbol(sym.CHAR, yytext().charAt(1)); }
"true" 		{ return new_symbol(sym.BOOL, true); }
"false" 	{ return new_symbol(sym.BOOL, false); }
"+" 		{ return new_symbol(sym.PLUS, yytext()); }
"-" 		{ return new_symbol(sym.MINUS, yytext()); }
"*" 		{ return new_symbol(sym.MUL, yytext()); }
"/" 		{ return new_symbol(sym.DIV, yytext()); }
"%" 		{ return new_symbol(sym.MOD, yytext()); }
"==" 		{ return new_symbol(sym.EQUAL, yytext()); }
"!=" 		{ return new_symbol(sym.NOT_EQ, yytext()); }
"<" 		{ return new_symbol(sym.LESS, yytext()); }
">" 		{ return new_symbol(sym.GREATER, yytext()); }
"<=" 		{ return new_symbol(sym.LESS_EQ, yytext()); }
">=" 		{ return new_symbol(sym.GREATER_EQ, yytext()); }
"&&" 		{ return new_symbol(sym.AND, yytext()); }
"||" 		{ return new_symbol(sym.OR, yytext()); }
"=" 		{ return new_symbol(sym.ASSIGN, yytext()); }
"++" 		{ return new_symbol(sym.INC, yytext()); }
"--" 		{ return new_symbol(sym.DEC, yytext()); }
"::" 		{ return new_symbol(sym.DOUBLEC, yytext()); }
";" 		{ return new_symbol(sym.SEMI, yytext()); }
"," 		{ return new_symbol(sym.COMMA, yytext()); }
"(" 		{ return new_symbol(sym.LPAREN, yytext()); }
")" 		{ return new_symbol(sym.RPAREN, yytext()); }
"[" 		{ return new_symbol(sym.LSQUARE, yytext()); }
"]" 		{ return new_symbol(sym.RSQUARE, yytext()); }
"{" 		{ return new_symbol(sym.LCURLY, yytext()); }
"}"			{ return new_symbol(sym.RCURLY, yytext()); }

// Comments
"//" 			 { yybegin(COMMENT); }
<COMMENT> .		 { yybegin(COMMENT); }
<COMMENT> "\r\n" { yybegin(YYINITIAL); }

// Tokens - regular expressions

[0-9]+  						{ return new_symbol(sym.NUMBER, Integer.parseInt (yytext())); }
([a-z]|[A-Z])[a-z|A-Z|0-9|_]* 	{ return new_symbol(sym.IDENT, yytext()); }


. { System.err.println("Leksicka greska ("+yytext()+") u liniji "+ (yyline+1) + " na poziciji " + yycolumn); }