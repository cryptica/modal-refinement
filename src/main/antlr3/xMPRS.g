grammar xMPRS;

options {
    output=AST; 
}

/*
 * LEXER RULES
 */

tokens {
    /* mPRS */  

    MPRS='mprs';

    REFINES='<=';

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

/*
 * ERROR HANDLING
 */

@parser::members {
  @Override
  public void reportError(RecognitionException e) {
    throw new IllegalTokenException(e);
  }
}

@lexer::members {
  @Override
  public void reportError(RecognitionException e) {
    throw new IllegalTokenException(e);
  }
}

ID          : ('a'..'z'|'A'..'Z')('a'..'z'|'A'..'Z'|'0'..'9')*;
WS          : (' '|'\n'|'\t'|'\r')+ { $channel = HIDDEN; };

/*
 * PARSER RULES
 */

mprs        : MPRS ID (OB process REFINES process rule* CB)? -> ^(MPRS[$ID] process process rule*);

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

