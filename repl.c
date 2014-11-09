#include <stdio.h>
#include <stdlib.h>

#include <editline/readline.h>

#include "mpc.h"

// TODO: shouldn't these be enumerated types and a static char** ?
#define NUMBER "number"
#define SYMBOL "symbol"
#define STRING "string"
#define REGEX "regex"
#define COMMENT "comment"
#define QEXPR "qexpr"
#define ADD "+"
#define SUB "-"
#define MUL "*"
#define DIV "/"
#define HEAD "head"
#define TAIL "tail"
#define LIST "list"
#define EVAL "eval"
#define JOIN "join"
#define LAMBDA "lambda"
#define DEF "def"
#define LET "let"
#define PRINT "prn"
#define AMPERS "&"
#define GT ">"
#define LT "<"
#define GE ">="
#define LE "<="
#define EQ "="
#define IF "if"

#ifdef DEBUG
  #include <assert.h>
  #define CHECK(COND) \
do { puts("Performing Assertion"); assert(COND); puts("Assertion passed"); } while(0)
#else
#define CHECK(COND)
#endif

#define LVAL_ASSERT(v, cond, fmt, ...) \
if (!(cond)) { \
  lval* err = lval_err(fmt, ##__VA_ARGS__); \
  lval_del(v); \
  return err; }

// forward declarations
struct lval;
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;
lenv* lenv_new(void);
void lenv_del(lenv* e);
lenv* lenv_copy(lenv* e);
void lval_print(lval* v);
lval* lval_eval(lenv* e, lval* v);
mpc_parser_t* Comment;
mpc_parser_t* Number;
mpc_parser_t* Symbol;
mpc_parser_t* String;
mpc_parser_t* Sexpr;
mpc_parser_t* Qexpr;
mpc_parser_t* Expr;
mpc_parser_t* Lajal;

typedef lval* (*lbuiltin)(lenv*, lval*);

typedef enum {
  LVAL_NUM,
  LVAL_STR,
  LVAL_SYM,
  LVAL_SEXPR,
  LVAL_QEXPR,
  LVAL_FUN,
  LVAL_ERR
} lval_type_t;

struct lval {
  lval_type_t type;

  long num;
  char* err;
  char* symbol;
  char* str;

  lbuiltin builtin;
  lenv* env;
  lval* formals;
  lval* body;

  int cell_count;
  lval** cell;
};

struct lenv {
  lenv* parent;

  int count;
  char** symbols;
  lval** values;
};

char* lval_type_name(lval_type_t t) {
  switch(t) {
    case LVAL_NUM: {
      return "Number";
    }
    case LVAL_SYM: {
      return "Symbol";
    }
    case LVAL_STR: {
      return "String";
    }
    case LVAL_SEXPR: {
      return "S-Expression";
    }
    case LVAL_QEXPR: {
      return "Q-Expression";
    }
    case LVAL_FUN: {
      return "Function";
    }
    case LVAL_ERR: {
      return "Error";
    }
    default: {
      return "Unknown";
    }
  }
}

lval* lval_num(long num) {
  lval* v = malloc(sizeof(lval));
  CHECK(v != NULL);

  v->type = LVAL_NUM;
  v->num = num;
  
  return v;
}

lval* lval_symbol(char* symbol) {
  lval* v = malloc(sizeof(lval));
  CHECK(v != NULL);

  v->type = LVAL_SYM;
  v->symbol = malloc(strlen(symbol));
  CHECK(v->symbol != NULL);
  strcpy(v->symbol, symbol);

  return v;
}

lval* lval_string(const char* string) {
  lval* v = malloc(sizeof(lval));
  CHECK(v != NULL);

  v->type = LVAL_STR;
  v->str = malloc(strlen(string));
  CHECK(v->str != NULL);
  strcpy(v->str, string);

  return v;
}

lval* lval_sexpr(void) {
  lval* v = malloc(sizeof(lval));
  CHECK(v != NULL);

  v->type = LVAL_SEXPR;
  v->cell_count = 0;
  v->cell = NULL;

  return v;
}

lval* lval_qexpr(void) {
  lval* v = malloc(sizeof(lval));
  CHECK(v != NULL);

  v->type = LVAL_QEXPR;
  v->cell_count = 0;
  v->cell = NULL;

  return v;
}

lval* lval_fun(lbuiltin func) {
  lval* v = malloc(sizeof(lval));
  CHECK(v != NULL);

  v->type = LVAL_FUN;
  v->builtin = func;

  return v;
}

lval* lval_lambda(lval* args, lval* body) {
  lval* v = malloc(sizeof(lval));
  CHECK(v != NULL);

  v->type = LVAL_FUN;
  v->builtin = NULL;
  v->env = lenv_new();
  v->formals = args;
  v->body = body;

  return v;
}

lval* lval_err(char* fmt, ...) {
  lval* v = malloc(sizeof(lval));
  CHECK(v != NULL);
  
  v->type = LVAL_ERR;

  va_list va;
  va_start(va, fmt);

  // TODO: cleanup magic numbers
  v->err = malloc(512 * sizeof(char));
  CHECK(v->err != NULL);
  vsnprintf(v->err, 511, fmt, va);
  v->err = realloc(v->err, strlen(v->err) * sizeof(char));
  va_end(va);

  return v;
}

lval* lval_add(lval* parent, lval* child) {
  parent->cell_count++;
  parent->cell = realloc(parent->cell, parent->cell_count * sizeof(lval*));
  parent->cell[parent->cell_count - 1] = child;
  return parent;
}

void lval_del(lval *v) {
  switch (v->type) {
    case LVAL_NUM: {
      break;
    }
    case LVAL_FUN: {
      if (v->builtin == NULL) {
        lenv_del(v->env);
        lval_del(v->formals);
        lval_del(v->body);
      }
      break;
    }
    case LVAL_SYM: {
      free(v->symbol);
      break;
    }
    case LVAL_STR: {
      free(v->str);
      break;
    }
    case LVAL_ERR: {
      free(v->err);
      break;
    }
    case LVAL_SEXPR:
    case LVAL_QEXPR: {
      for (int i = 0; i < v->cell_count; i++) {
        lval_del(v->cell[i]);
      }
      free(v->cell);
      break;
    }
  }
  free(v);
}

lval* lval_copy(lval* v) {
  lval* cpy;

  switch (v->type) {
    case LVAL_NUM: {
      cpy = lval_num(v->num);
      break;
    }
    case LVAL_SYM: {
      cpy = lval_symbol(v->symbol);
      break;
    }
    case LVAL_STR: {
      cpy = lval_string(v->str);
      break;
    }
    case LVAL_SEXPR:
    case LVAL_QEXPR: {
      cpy = malloc(sizeof(lval));
      CHECK(cpy != NULL);
      cpy->type = v->type;
      cpy->cell_count = v->cell_count;
      cpy->cell = malloc(cpy->cell_count * sizeof(lval*));
      CHECK(cpy->cell != NULL);
      for (int i = 0; i < cpy->cell_count; i++) {
        cpy->cell[i] = lval_copy(v->cell[i]);
      }
      break;
    }
    case LVAL_FUN: {
      if (v->builtin != NULL) {
        cpy = lval_fun(v->builtin);
      }
      else {
        cpy = lval_lambda(NULL, NULL);
        cpy->env = lenv_copy(v->env);
        cpy->formals = lval_copy(v->formals);
        cpy->body = lval_copy(v->body);
      }
      break;
    }
    case LVAL_ERR: {
      cpy = lval_err(v->err);
    }
  }

  return cpy;
}

lval* lval_pop(lval* v, int idx){
  CHECK(idx >= 0);

  lval* result = v->cell[idx];
  CHECK(result != NULL);

  memmove(&v->cell[idx], &v->cell[idx+1], (v->cell_count - idx - 1) * sizeof(lval*));
  v->cell_count--;
  v->cell = realloc(v->cell, v->cell_count * sizeof(lval*));

  return result;
}

lval* lval_take(lval* v, int idx){
  CHECK(idx >= 0);

  lval* result = lval_pop(v, idx);
  lval_del(v);

  return result;
}

lval* lval_join(lval* result, lval* part) {
  while (part->cell_count > 0) {
    lval_add(result, lval_pop(part, 0));
  }

  lval_del(part);
  return result;
}

lenv* lenv_new(void) {
  lenv* env = malloc(sizeof(lenv));
  CHECK(env != NULL);

  env->parent = NULL;

  env->count = 0;
  env->symbols = NULL;
  env->values = NULL;

  return env;
}

void lenv_del(lenv* e) {
  for (int i = 0; i < e->count; i++) {
    free(e->symbols[i]);
    lval_del(e->values[i]);
  }

  free(e->symbols);
  free(e->values);
  free(e);
}

lenv* lenv_copy(lenv* e) {
  lenv* cpy = lenv_new();

  cpy->parent = e->parent;
  cpy->count = e->count;
  cpy->symbols = malloc(cpy->count * sizeof(char*));
  cpy->values = malloc(cpy->count * sizeof(lval*));

  for (int i = 0; i < cpy->count; i++) {
    cpy->symbols[i] = malloc(strlen(e->symbols[i]) * sizeof(char));
    strcpy(cpy->symbols[i], e->symbols[i]);

    cpy->values[i] = lval_copy(e->values[i]);
  }

  return cpy;
}

static int lenv_get_idx(lenv* e, lval* var) {
  for (int i = 0; i < e->count; i++) {
    if (strcmp(e->symbols[i], var->symbol) == 0) {
      return i;
    }
  }
  return -1;
}

lval* lenv_get(lenv* e, lval* var) {
  int idx = lenv_get_idx(e, var);

  return idx != -1 ?
    lval_copy(e->values[idx]) :
    (e->parent != NULL ?
      lenv_get(e->parent, var) :
      lval_err("Unbound variable: '%s'", var->symbol));
}

void lenv_put(lenv* e, lval* sym, lval* var) {
  CHECK(var->type != LVAL_ERR);

  int idx = lenv_get_idx(e, sym);
  lval* new = lval_copy(var);
  // if variable already exists
  if (idx != -1) {
    lval* old = e->values[idx];
    e->values[idx] = new;
    lval_del(old);
  }
  else {
    e->count++;
    e->symbols = realloc(e->symbols, e->count * sizeof(char*));
    e->values = realloc(e->values, e->count * sizeof(lval*));
    e->symbols[e->count - 1] = malloc(strlen(sym->symbol) * sizeof(char));
    CHECK(e->symbols[e->count - 1] != NULL);
    
    strcpy(e->symbols[e->count - 1], sym->symbol);
    e->values[e->count - 1] = new;
  }
}

void lenv_def(lenv* e, lval* sym, lval* var) {
  // get to the topmost environment
  while(e->parent != NULL) {
    e = e->parent;
  }

  lenv_put(e, sym, var);
}

lval* lval_read_num(mpc_ast_t* ast) {
  errno = 0;
  long num = strtol(ast->contents, NULL, 10);
  return errno != ERANGE ? lval_num(num) : lval_err("Invalid Number!");
}

lval* lval_read_str(mpc_ast_t* ast) {
  // Get rid of the quotes
  ast->contents[strlen(ast->contents)-1] = '\0';
  char* unescaped = malloc(strlen(ast->contents+1));
  strcpy(unescaped, ast->contents+1);

  unescaped = mpcf_unescape(unescaped);

  lval* str = lval_string(unescaped);

  free(unescaped);
  return str;
}

lval* lval_read(mpc_ast_t* ast) {
  if (strstr(ast->tag, NUMBER)) {
    return lval_read_num(ast);
  }
  if (strstr(ast->tag, SYMBOL)) {
    return lval_symbol(ast->contents);
  }
  if (strstr(ast->tag, STRING)) {
    return lval_read_str(ast);
  }

  lval* result = NULL;
  // not sure the below comparison is needed
  // strcmp(ast->tag, ">") == 0 || strstr(ast->tag, "regex")
  if (strstr(ast->tag, ">")) {
    if (strstr(ast->tag, QEXPR)) {
      result = lval_qexpr();
    }
    else {
      result = lval_sexpr();
    }
  }

  for (int i = 0; i < ast->children_num; i++) {
    mpc_ast_t* child = ast->children[i];

    if (strcmp(child->tag, REGEX) == 0 ||
        strstr(child->tag, COMMENT) ||
        strcmp(child->contents, "(") == 0 ||
        strcmp(child->contents, ")") == 0 ||
        strcmp(child->contents, "{") == 0 ||
        strcmp(child->contents, "}") == 0) {
      continue;
    }
    result = lval_add(result, lval_read(child));
  }

  return result;
}

void lval_print_expr(lval* v, char open, char close) {
  putchar(open);
  for (int i = 0; i < v->cell_count; i++) {
    lval_print(v->cell[i]);

    if (i < (v->cell_count - 1)) {
      putchar(' ');
    }
  }
  putchar(close);
}

void lval_print_str(lval* v) {
  char* escaped = malloc(strlen(v->str));
  strcpy(escaped, v->str);

  escaped = mpcf_escape(escaped);
  printf("\"%s\"", escaped);

  free(escaped);
}

void lval_print(lval* v) {
  CHECK(v != NULL);

  switch (v->type) {
    case LVAL_NUM: {
      printf("%ld", v->num);
      break;
    }
    case LVAL_SYM: {
      printf("%s", v->symbol);
      break;
    }
    case LVAL_STR: {
      lval_print_str(v);
      break;
    }
    case LVAL_SEXPR: {
      lval_print_expr(v, '(', ')');
      break;
    }
    case LVAL_QEXPR: {
      lval_print_expr(v, '{', '}');
      break;
    }
    case LVAL_FUN: {
      if (v->builtin != NULL) {
        printf("<function>");
      }
      else {
        printf("(%s ", LAMBDA);
        lval_print(v->formals);
        putchar(' ');
        lval_print(v->body);
        putchar(')');
      }
      break;
    }
    case LVAL_ERR: {
      printf("Error: %s", v->err);
      break;
    }
  }
}

void lval_println(lval* v) {
  lval_print(v);
  putchar('\n');
}


// typedef struct mpc_ast_t {
//   char *tag;
//   char *contents;
//   mpc_state_t state;
//   int children_num;
//   struct mpc_ast_t** children;
// } mpc_ast_t;

lval* lval_builtin_op(lenv* e, lval* v, char* operator) {
  CHECK(v != NULL);
  CHECK(operator != NULL);

  // for the supported operators: +, -, *, /
  char op = operator[0];
  CHECK(op == '+' || op == '-' || op == '*' || op == '/');

  // all arguments must be numbers
  for (int i = 0; i < v->cell_count; i++) {
    if (v->cell[i]->type != LVAL_NUM) {
      lval_del(v);
      return lval_err("Arguments must be numbers in arithmetic operations!");
    }
  }

  // pop first value
  lval* result = lval_pop(v, 0);
  lval* parcel = NULL;

  if (op == '-' && v->cell_count == 0) {
    result->num = -result->num;
  }

  while (v->cell_count > 0) {
    parcel = lval_pop(v, 0);

    switch (op) {
      case '+': {
        result->num += parcel->num;
        break;
      }
      case '-': {
        result->num -= parcel->num;
        break;
      }
      case '*': {
        result->num *= parcel->num;
        break;
      }
      case '/': {
        if (parcel->num == 0) {
          lval_del(parcel);
          lval_del(v);
          lval_del(result);
          return lval_err("Division by zero!");
        }
        result->num /= parcel->num;
        break;
      }
    }

    lval_del(parcel);
  }

  lval_del(v);
  return result;
}

lval* lval_builtin_add(lenv* e, lval* v) {
  return lval_builtin_op(e, v, ADD);
}

lval* lval_builtin_sub(lenv* e, lval* v) {
  return lval_builtin_op(e, v, SUB);
}

lval* lval_builtin_mul(lenv* e, lval* v) {
  return lval_builtin_op(e, v, MUL);
}

lval* lval_builtin_div(lenv* e, lval* v) {
  return lval_builtin_op(e, v, DIV);
}

lval* lval_builtin_ord(lenv* e, lval* v, char* op){
  CHECK(v != NULL);
  CHECK(op != NULL);

  LVAL_ASSERT(v, v->cell_count == 2,
    "%s function only works on 2 arguments", op);
  // all arguments must be numbers
  for (int i = 0; i < v->cell_count; i++) {
    LVAL_ASSERT(v, v->cell[i]->type == LVAL_NUM,
      "Arguments must be numbers in comparison operations!");
  }

  // initializing to silence warning
  int result = 0;
  int l = v->cell[0]->num,
    r = v->cell[1]->num;

  if (strcmp(op, GT) == 0) {
    result = l > r;
  }
  else if (strcmp(op, LT) == 0) {
    result = l < r;
  }
  else if (strcmp(op, GE) == 0) {
    result = l >= r;
  }
  else if (strcmp(op, LE) == 0) {
    result = l<= r;
  }

  lval_del(v);
  return lval_num(result);
}

lval* lval_builtin_gt(lenv* e, lval* v) {
  return lval_builtin_ord(e, v, GT);
}

lval* lval_builtin_lt(lenv* e, lval* v) {
  return lval_builtin_ord(e, v, LT);
}

lval* lval_builtin_ge(lenv* e, lval* v) {
  return lval_builtin_ord(e, v, GE);
}

lval* lval_builtin_le(lenv* e, lval* v) {
  return lval_builtin_ord(e, v, LE);
}

int lval_eq(lval* x, lval* y) {
  // 2 values are equal if:
  // they are the same type
  if (x->type != y->type) {
    return 0;
  }
  switch (x->type) {
    case LVAL_NUM: {
      // their values are the same
      return x->num == y->num;
      break;
    }
    case LVAL_SYM: {
      // their are the same symbol
      return strcmp(x->symbol, y->symbol) == 0;
      break;
    }
    case LVAL_STR: {
      // their are the same string
      return strcmp(x->str, y->str) == 0;
      break;
    }
    case LVAL_SEXPR:
    case LVAL_QEXPR: {
      // all of the elements in the list are the same
      if (x->cell_count != y->cell_count) {
        return 0;
      }
      for (int i = 0; i < x->cell_count; i++) {
        if (!lval_eq(x->cell[i], y->cell[i])) {
          return 0;
        }
      }
      return 1;
      break;
    }
    case LVAL_FUN: {
      // they are the same builtin function
      if (x->builtin != NULL || y->builtin != NULL) {
        return x->builtin == y->builtin;
      }
      // their args and body are the same
      else {
        return lval_eq(x->formals, y->formals) && lval_eq(x->body, y->body);
      }
    }
    case LVAL_ERR: {
      // their are the same error?
      return strcmp(x->err, y->err) == 0;
      break;
    }
  }
}

lval* lval_builtin_eq(lenv* e, lval* v) {
  LVAL_ASSERT(v, v->cell_count == 2,
    "Equality only takes 2 arguments!");

  int result = lval_eq(v->cell[0], v->cell[1]);
  lval_del(v);
  return lval_num(result);
}

lval* lval_builtin_if(lenv* e, lval* v) {
  LVAL_ASSERT(v, v->cell_count == 3,
    "If-function only takes 3 arguments!");
  LVAL_ASSERT(v, v->cell[0]->type == LVAL_NUM,
    "Argument 1 must be bool!");
  LVAL_ASSERT(v, v->cell[1]->type == LVAL_QEXPR && v->cell[2]->type == LVAL_QEXPR,
    "Arguments 2 and 3 must be Q-Expressions!");

  v->cell[1]->type = LVAL_SEXPR;
  v->cell[2]->type = LVAL_SEXPR;

  lval* result = v->cell[0]->num ?
    lval_eval(e, lval_pop(v, 1)) :
    lval_eval(e, lval_pop(v, 2));

  lval_del(v);
  return result;
}

lval* lval_builtin_head(lenv* e, lval* v) {
  // head only takes 1 arg
  LVAL_ASSERT(v, v->cell_count == 1,
    "Invalid number of arguments passed to built-in function head."
    " Expected %d, found %d", 1, v->cell_count);
  // head only works on Q-Expressions
  LVAL_ASSERT(v, v->cell[0]->type == LVAL_QEXPR,
    "Argument must be of type QEXPR.");
  // Q-Expression must not be empty
  LVAL_ASSERT(v, v->cell[0]->cell_count != 0,
    "Argument must be non-empty list.");

  // take first arg
  lval* lst = lval_take(v, 0);
  while (lst->cell_count > 1) {
    lval_del(lval_pop(lst, 1));
  }
  return lst;
}

lval* lval_builtin_tail(lenv* e, lval* v) {
  // tail only takes 1 arg
  LVAL_ASSERT(v, v->cell_count == 1,
    "Invalid number of arguments passed to built-in function tail. "
    "Expected %d, found %d", 1, v->cell_count);
  // tail only works on Q-Expressions
  LVAL_ASSERT(v, v->cell[0]->type == LVAL_QEXPR,
    "Argument must be of type QEXPR.");
  // Q-Expression must not be empty
  LVAL_ASSERT(v, v->cell[0]->cell_count != 0,
    "Argument must be non-empty list.");
  
  lval* result = lval_take(v, 0);
  lval_del(lval_pop(result, 0));
  return result;
}

lval* lval_builtin_list(lenv* e, lval* v) {
  v->type = LVAL_QEXPR;
  return v;
}

lval* lval_builtin_eval(lenv* e, lval* v) {
  // eval only takes 1 arg
  LVAL_ASSERT(v, v->cell_count == 1,
    "Invalid number of arguments passed to built-in function eval."
    "Expected %d, found %d.", 1, v->cell_count);
  // eval only works on Q-Expressions
  LVAL_ASSERT(v, v->cell[0]->type == LVAL_QEXPR,
    "Argument must be of type QEXPR.");

  lval* result = lval_take(v, 0);
  result->type = LVAL_SEXPR;
  return lval_eval(e, result);
}

lval* lval_builtin_join(lenv* e, lval* v) {
  for (int i = 0; i < v->cell_count; i++) {
    LVAL_ASSERT(v->cell[i], v->cell[i]->type == LVAL_QEXPR,
      "Built-in function 'join' passed incorrect type.");
  }

  lval* result = lval_pop(v, 0);

  while(v->cell_count > 0) {
    result = lval_join(result, lval_pop(v, 0));
  }

  lval_del(v);
  return result;
}

lval* lval_var(lenv* e, lval* v, char* func) {
  LVAL_ASSERT(v, v->cell[0]->type == LVAL_QEXPR,
    "%s passed incorrect type.", func);

  lval* symbols = v->cell[0];
  for (int i = 0; i < symbols->cell_count; i++) {
    LVAL_ASSERT(v, symbols->cell[i]->type == LVAL_SYM,
      "def can't define non-symbol.");
  }

  LVAL_ASSERT(v, symbols->cell_count == (v->cell_count - 1),
    "expected equal number of symbols and values.");

  for (int i = 0; i < symbols->cell_count; i++) {
    if(strcmp(func, DEF) == 0) {
      lenv_def(e, symbols->cell[i], v->cell[i+1]);
    }
    else if (strcmp(func, LET) == 0) {
      lenv_put(e, symbols->cell[i], v->cell[i+1]);
    }
  }

  lval_del(v);
  return lval_sexpr();
}

lval* lval_builtin_def(lenv* e, lval* v) {
  return lval_var(e, v, DEF);
}

lval* lval_builtin_let(lenv* e, lval* v) {
  return lval_var(e, v, LET);
}

lval* lval_builtin_lambda(lenv* e, lval* v) {
  LVAL_ASSERT(v, v->cell_count == 2,
    "Invalid number of arguments passed to built-in function %s.", LAMBDA);

  LVAL_ASSERT(v, v->cell[0]->type == LVAL_QEXPR && v->cell[1]->type == LVAL_QEXPR,
    "%s passed incorrect type.", LAMBDA);

  lval* symbols = v->cell[0];
  for (int i = 0; i < symbols->cell_count; i++) {
    LVAL_ASSERT(v, symbols->cell[i]->type == LVAL_SYM,
      "arguments must all be symbols.");
  }

  lval* args = lval_pop(v, 0);
  lval* body = lval_pop(v, 0);

  lval* lbda = lval_lambda(args, body);

  lval_del(v);
  return lbda;
}

lval* lval_builtin_print(lenv* e, lval* v) {
  for (int i = 0; i < v->cell_count; i++) {
    lval_print(v->cell[i]);
    putchar(' ');
  }

  putchar('\n');
  lval_del(v);

  return lval_sexpr();
}

lval* lval_builtin_load(lenv* e, lval* v) {
  LVAL_ASSERT(v, v->cell_count == 1,
    "Wrong number of arguments passed to load. Expected 1, found %d.",
    v->cell_count);
  LVAL_ASSERT(v, v->cell[0]->type == LVAL_STR,
    "Load only accepts a string as argument.");

  mpc_result_t r;
  if (mpc_parse_contents(v->cell[0]->str, Lajal, &r)) {
    lval* expr = lval_read(r.output);
    mpc_ast_delete(r.output);

    while (expr->cell_count) {
      lval* x = lval_eval(e, lval_pop(expr, 0));

      if (x->type == LVAL_ERR) {
        lval_println(x);
      }
      lval_del(x);
    }

    lval_del(expr);
    lval_del(v);

    return lval_sexpr();
  }
  else {
    char* err_msg = mpc_err_string(r.error);
    mpc_err_delete(r.error);

    lval* err = lval_err("Could not load file %s", err_msg);
    free(err_msg);
    lval_del(v);

    return err;
  }
}

lval* lval_call(lenv* e, lval* f, lval* v) {
  // it's a builtin function, compute result
  if (f->builtin != NULL) {
    return f->builtin(e, v);
  }

  int expected = 0;

  // it's a user defined function
  // bind each arg to the formals in f
  while (v->cell_count > 0) {
    // deals with too much arguments
    LVAL_ASSERT(v, f->formals->cell_count > 0,
      "Too many arguments passed to function."
      " Expected %d, found %d.", expected, expected + v->cell_count);
    expected++;
    
    lval* symb = lval_pop(f->formals, 0);

    if (strcmp(symb->symbol, AMPERS) == 0) {
      LVAL_ASSERT(v, f->formals->cell_count == 1,
        "Incorrect syntax for variadic arguments. Expected symbol after '&'");

      expected--;

      // pop list symbol
      lval* lst = lval_pop(f->formals, 0);
      // v contains all arguments that make the list
      lenv_put(f->env, lst, lval_builtin_list(e, v));
      lval_del(lst);
      // also delete '&' struct
      lval_del(symb);
      break;
    }

    lval* arg = lval_pop(v, 0);
    lenv_put(f->env, symb, arg);
    lval_del(symb);
    lval_del(arg);
  }

  if (f->formals->cell_count > 0 &&
    strcmp(f->formals->cell[0]->symbol, AMPERS) == 0) {

    LVAL_ASSERT(v, f->formals->cell_count == 2,
      "Incorrect syntax for variadic arguments. Expected symbol after '&'");

    lval_del(lval_pop(f->formals, 0));
    // pop list symbol
    lval* lst_sym = lval_pop(f->formals, 0);
    lval* empty_lst = lval_qexpr();
    lenv_put(f->env, lst_sym, empty_lst);
    lval_del(lst_sym);
    lval_del(empty_lst);
  }

  // deals with too few arguments
  LVAL_ASSERT(v, f->formals->cell_count == 0,
    "Too few arguments passed to function."
    " Expected %d, found %d.", expected + f->formals->cell_count, expected + v->cell_count);

  lval_del(v);
  // with e as the parent env of f->env
  f->env->parent = e;

  // eval the body of f with bound formals
  return lval_builtin_eval(f->env, lval_add(lval_sexpr(), lval_copy(f->body)));
}

lval* lval_eval_sexpr(lenv* e, lval* v) {
  CHECK(v != NULL);
  // evaluate all children
  for (int i = 0; i < v->cell_count; i++) {
    v->cell[i] = lval_eval(e, v->cell[i]);
    // check for errors
    // if (v->cell[i]->type == LVAL_ERR) {
    //   return lval_take(v, i);
    // }
  }

  // check for errors
  // TODO: couldn't this be implemented in the above cycle? why run 2 fors?
  for (int i = 0; i < v->cell_count; ++i) {
    if (v->cell[i]->type == LVAL_ERR) {
      return lval_take(v, i);
    }
  }

  if (v->cell_count == 0) {
    return v;
  }
  if (v->cell_count == 1) {
    return lval_take(v, 0);
  }

  // now we have an expression with more than one child
  // extract symbol
  lval* result = NULL;
  lval* lval_sym = lval_pop(v, 0);

  if(lval_sym->type != LVAL_FUN) {
    lval_del(v);
    result = lval_err("first element is not a function");
  }
  else {
    result = lval_call(e, lval_sym, v);
  }

  lval_del(lval_sym);

  return result;
}

lval* lval_eval(lenv* e, lval* v) {
  if (v->type == LVAL_SYM) {
    lval* var = lenv_get(e, v);
    lval_del(v);

    return var;
  }
  if (v->type == LVAL_SEXPR) {
    return lval_eval_sexpr(e, v);
  }

  return v;
}

void lenv_add_builtin(lenv* e, char* name, lbuiltin func) {
  lval* sym = lval_symbol(name);
  lval* var = lval_fun(func);
  
  lenv_put(e, sym, var);
  
  lval_del(sym);
  lval_del(var);
}

void lenv_register_builtins(lenv* e) {
  // MATH
  lenv_add_builtin(e, ADD, lval_builtin_add);
  lenv_add_builtin(e, SUB, lval_builtin_sub);
  lenv_add_builtin(e, MUL, lval_builtin_mul);
  lenv_add_builtin(e, DIV, lval_builtin_div);

  // LISP FUNCTIONS
  lenv_add_builtin(e, HEAD, lval_builtin_head);
  lenv_add_builtin(e, TAIL, lval_builtin_tail);
  lenv_add_builtin(e, LIST, lval_builtin_list);
  lenv_add_builtin(e, EVAL, lval_builtin_eval);
  lenv_add_builtin(e, JOIN, lval_builtin_join);
  lenv_add_builtin(e, DEF, lval_builtin_def);
  lenv_add_builtin(e, LET, lval_builtin_let);
  lenv_add_builtin(e, LAMBDA, lval_builtin_lambda);
  lenv_add_builtin(e, GT, lval_builtin_gt);
  lenv_add_builtin(e, LT, lval_builtin_lt);
  lenv_add_builtin(e, GE, lval_builtin_ge);
  lenv_add_builtin(e, LE, lval_builtin_le);
  lenv_add_builtin(e, EQ, lval_builtin_eq);
  lenv_add_builtin(e, IF, lval_builtin_if);
  lenv_add_builtin(e, PRINT, lval_builtin_print);
}

int main(int argc, char const *argv[]) {
  char* input;

  // GRAMMAR
  Comment = mpc_new(COMMENT);
  Number = mpc_new(NUMBER);
  Symbol = mpc_new(SYMBOL);
  String = mpc_new(STRING);
  Sexpr = mpc_new("sexpr");
  Qexpr = mpc_new(QEXPR);
  Expr = mpc_new("expr");
  Lajal = mpc_new("lajal");

  mpca_lang(MPCA_LANG_DEFAULT,
    "\
    comment : /;[^\\r\\n]*/ ; \
    number : /-?[0-9]+/ ; \
    symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/ ; \
    string  : /\"(\\\\.|[^\"])*\"/ ; \
    sexpr : '(' <expr>* ')'; \
    qexpr : '{' <expr>* '}'; \
    expr : <comment> | <number> | <symbol> | <string> | <sexpr> | <qexpr> ; \
    lajal : /^/ <expr>* /$/ ; \
    ", Comment, Number, Symbol, String, Sexpr, Qexpr, Expr, Lajal);

  // create environment and register builtin functions
  lenv* env = lenv_new();
  lenv_register_builtins(env);

  if (argc > 1) {
    for (int i = 1; i < argc; i++) {
      lval* args = lval_add(lval_sexpr(), lval_string(argv[i]));

      lval* x = lval_builtin_load(env, args);

      if (x->type == LVAL_ERR) {
        lval_println(x);
      }

      lval_del(x);
    }
  }
  else {
    puts("lajal Version 0.0.1-SNAPSHOT");
    puts("Press Ctrl+C to exit\n");

    while(1) {
      // Read input
      input = readline("lajal > ");
      add_history(input);

      mpc_result_t r;
      if (mpc_parse("<stdin>", input, Lajal, &r)) {
        // If it conforms to the grammar, read and eval the AST
        //mpc_ast_print(r.output);
        lval* x = lval_eval(env, lval_read(r.output));
        lval_println(x);
        lval_del(x);
        mpc_ast_delete(r.output);
      } else {
        // Otherwise print the error
        mpc_err_print(r.error);
        mpc_err_delete(r.error);
      }

      free(input);
    }
  }

  lenv_del(env);
  mpc_cleanup(8, Comment, Number, Symbol, String, Sexpr, Qexpr, Expr, Lajal);

  return 0;
}
