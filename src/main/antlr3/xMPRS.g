grammar xMPRS;

options {
    output=AST; 
}

/*------------------------------------------------------------------
 * LEXER RULES
 *------------------------------------------------------------------*/

tokens {
    MPRS='mprs';

    /* Options */

    INITIAL='initial';

    /* Process */

    PROCESS;
    CONSTANT;
    EMPTY;
    PARALLEL;
    SEQUENTIAL;

    /* Rule */

    MAY_RULE;
    MUST_RULE;

    /* Action */

    ACTION;

    /* Special */

    OB='[';
    CB=']';   
    OP='(';
    CP=')';
    BAR='|';    
    DOT='.';
    UNDERSCORE='_';
    QUESTION='?';
    EXCLAMATION='!';
}

ID          : ('a'..'z'|'A'..'Z')('a'..'z'|'A'..'Z'|'0'..'9')*;
STRING      : '"' (options {greedy=false;}: . )* '"';
WS          : (' '|'\n'|'\t'|'\r')+ { $channel = HIDDEN; };

/*------------------------------------------------------------------
 * PARSER RULES
 *------------------------------------------------------------------*/

mprs        : MPRS ID (OB INITIAL process rule* CB)? -> ^(MPRS[$ID] process rule*);


/* Process */

process     : parallel;

parallel    : sequential ( BAR sequential )* -> ^(PARALLEL sequential+);

sequential  : elemental ( DOT elemental )* -> ^(SEQUENTIAL elemental+);

elemental   : UNDERSCORE -> ^(EMPTY)
            | ID -> ^(CONSTANT[$ID])
            | OP process CP -> process;

/* Rule */

rule        : process action rule_type process ->
              ^(rule_type process action process);
rule_type   : QUESTION -> ^(MAY_RULE)
            | EXCLAMATION -> ^(MUST_RULE);

/* Action */

action      : ID -> ^(ACTION[$ID]);

