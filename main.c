/*
verifica se 2 proposizioni logiche sono equivalenti
es esempio: A xor B \eq !(B or A)

supporto per simboli logici e denominazioni:

| Operazione Logica | Simbolo Corso / Java | Simbolo Logico Standard | Denominazione |
| :--- | :---: | :---: | :--- |
| **Negazione** | `!` | $\neg$ | NOT (non) |
| **Congiunzione** | `&&` | $\land$ | AND (e) |
| **Disgiunzione Inclusiva** | `\|\|` | $\lor$ | OR (o / oppure inclusivo) |
| **Implicazione Materiale** | `==>` | $\implies$ | Se ... allora |
| **Bicondizionale** | `<==>` | $\iff$ | Se e solo se |
| **Disgiunzione Esclusiva** | `<=!=>` | $\oplus$ (o XOR) | OR esclusivo (negato del bicondizionale) |


Sintassi semplici accettate per denominazioni:
- var1 AND/OR/Implicazione/Bicondizionale/XOR var2
- (var1 AND/OR/Implicazione/Bicondizionale/XOR var2)
- not var1

Sintassi semplici accettate per simboli:
- var1 && o || o ==> o <=!=> var2
- (var1 && o || o ==> o <=!=> var2)
- !var1

sintassi complesse accettate:
- sub proposizioni in all'interno delle ()
es: (var1 and var2) or var3

variabili speciali(costanti)
- true (1 in simboli logici)
- false (0 in simboli logici)
es: true && var1 AND (var2 ==> var3)

Funzioni:
- genera la tabella di verità per una proposizione logica
- confronta due proposizioni logiche per verificare la loro equivalenza

Logica per gestire:
1. pareser che converta una proposizione logica in un albero 
2. attraversamento dell albero con DFS 
3. provare ogni combinazione possibile delle variabili date nelle preposizioni logiche

regole parsing:
- priorita parentesi -> si generano 1 nodo figlio contenente il contenuto della parentesi
- lettura da sinistra a destra
- priorita operazioni logiche (NOT, AND, OR, IMPLIES, IFF, XOR)

attraversamento dell albero:
- si parte dal nodo radice e si scende fino ai nodi foglia
- si valuta il valore di ogni nodo in base alle operazioni logiche
- si risale all'indietro per calcolare il valore della proposizione complessiva

esempio: var1 OR var2 AND var3
       and
      /   \ 
    or     var3
  /    \ 
var1   var2

esempio: var1 OR (var2 AND var3)
      or
    /    \ 
var1      and
         /   \ 
      var2   var3


ottimizzationi logiche future:
- eliminazione nodi e subnodi sempre veri/false
- eliminazione nodi e sub nodi identita tipo: var1 AND var1 = var1

ottimizzazioni sw:
- multithreading per generazione tabella di verità
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define VAR_NAME_SIZE 16
#define MAX_STR_SIZE 1024

typedef enum {
    NOT,
    AND,
    OR,
    IMPLIES,
    IFF,
    XOR
} op;

static op vNOT = NOT;
static op vAND = AND;
static op vOR = OR;
static op vIMPLIES = IMPLIES;
static op vIFF = IFF;
static op vXOR = XOR;

typedef enum {
    FALSE = 0,
    TRUE = 1
} accvalue;

static accvalue vFALSE = FALSE;
static accvalue vTRUE = TRUE;

typedef struct node node;

typedef struct {
    char name[VAR_NAME_SIZE];
    accvalue value;
} var;

typedef struct node {
    int isop;       // indica se è un operazione o una variabile
    int isunaryop;  // indica se è un operazione unaria tipo: NOT
    int isconstant; // indica se è una costante tipo: true o false
    int isbracket;  // indica se è una parentesi aperta o chiusa

    accvalue value; // valore della costante
    op operation;   // tipo di oeprazione: AND, OR, ...
    var* var;       // puntatore all array delle variabili 

    struct node* operans[2]; // nodi figli
} node;


typedef struct stack {
    node* data;
    struct stack* next;
} stack;

typedef struct coda {
    node* data;
    struct coda* next;
} coda;

typedef struct {
    node* root;
    var** vars;
    int vars_count;

    coda* postfix; // puntatore all'array dei nodi in notazione postfissa
} tree;

void add_ref_to_var(var* v, node* n);

node* new_node(int isop, int isunaryop, int isconstant, int isbracket, const void* value) {
    node* tmp = (node*) calloc(1, sizeof(node));
    
    if(!tmp) { 
        perror("Errore calloc nuovo nodo\n");
        exit(1);
    }

    tmp->isop = isop;
    tmp->isunaryop = isunaryop;
    tmp->isconstant = isconstant;
    tmp->isbracket = isbracket;

    if (isconstant) {
        tmp->value = *(accvalue*)value;
    } else if (isop) {
        tmp->operation = *(op*)value;
    } else {
        // printf("Allocating variable node with value: %s\n", ((var*)value)->name);
        tmp->var = (var*)value;
    }

    return tmp;
}

tree* new_tree() {
    tree* tmp = (tree*) calloc(1, sizeof(tree));
    tmp->root = NULL;
    tmp->vars = NULL;
    tmp->vars_count = 0;

    return tmp;
}

int varname_ckeck(var** vars, int vars_count, char* name) {
    if (vars == NULL) {
        return 0;
    }
    for (int i = 0; i < vars_count; i++) {
        if (vars[i] != NULL && strcmp(vars[i]->name, name) == 0) {
            return 1; // variable already exists
        }
    }
    return 0; // variable does not exist
}

var* new_var(char* name, accvalue initalvalue) {
    var* tmp = (var*) calloc(1, sizeof(var));
    
    if (!tmp) {
        perror("Errore calloc nuova variabile\n");
        exit(1);
    }

    strcpy(tmp->name, name);
    tmp->name[VAR_NAME_SIZE - 1] = '\0'; // Ensure null-termination
    tmp->value = initalvalue;

    return tmp;
}

void add_new_var(tree* a, char* name, accvalue initalvalue) {
    // check if variable already exists with that name
    if(varname_ckeck(a->vars, a->vars_count, name)) {
        fprintf(stderr, "Errore: variabile %s già esistente\n", name);
        exit(1);
    }

    var* tmp = new_var(name, initalvalue);

    // resize vars in tree
    if (a->vars == NULL || a->vars_count == 0) {
        a->vars = (var**) calloc(1, sizeof(var*));
    } else {
        var** resized = (var**) realloc(a->vars, sizeof(var*) * (a->vars_count + 1));

        if (!resized) {
            perror("Errore realloc in tree->vars\n");
            exit(1);
        }

        a->vars = resized;
    }

    a->vars[a->vars_count] = tmp;
    a->vars_count++;
}

void add_existing_var(tree* a, var* v) {
    // check if variable already exists with that name
    if(varname_ckeck(a->vars, a->vars_count, v->name)) {
        fprintf(stderr, "Errore: variabile %s già esistente\n", v->name);
        exit(1);
    }

    // resize vars in tree
    if (a->vars == NULL || a->vars_count == 0) {
        a->vars = (var**) calloc(1, sizeof(var*));
    } else {
        var** resized = (var**) realloc(a->vars, sizeof(var*) * (a->vars_count + 1));

        if (!resized) {
            perror("Errore realloc in tree->vars\n");
            exit(1);
        }

        a->vars = resized;
    }

    a->vars[a->vars_count] = v;
    a->vars_count++;
}

//debug
void print_vars_table(tree* a) {
    printf("Variabili:\n");
    for (int i = 0; i < a->vars_count; i++) {
        printf("%s : %s\n", a->vars[i]->name, a->vars[i]->value == TRUE ? "true" : "false");
    }
}

//       or
//     /    \ 
// var1      and
//          /   \ 
//       var2   var3
void print_node_label(node* n) {
    if (n->isop) {
        switch (n->operation) {
            case NOT: printf("NOT"); break;
            case AND: printf("AND"); break;
            case OR: printf("OR"); break;
            case IMPLIES: printf("IMPLIES"); break;
            case IFF: printf("IFF"); break;
            case XOR: printf("XOR"); break;
        }
    } else if (n->isconstant) {
        printf("%s", n->value == TRUE ? "true" : "false");
    } else if (n->var != NULL) {
        printf("%s (%s)", n->var->name, n->var->value == TRUE ? "true" : "false");
    }
}

void print_tree_ascii(node* n, const char* prefix, int is_last, int is_root) {
    if (n == NULL) {
        return;
    }

    printf("%s", prefix);
    if (!is_root) {
        printf("%s", is_last ? "`-- " : "|-- ");
    }
    print_node_label(n);
    printf("\n");

    char child_prefix[1024];
    snprintf(child_prefix, sizeof(child_prefix), "%s%s", prefix,
             is_root ? "" : (is_last ? "    " : "|   "));

    int child_count = (n->operans[0] != NULL) + (n->operans[1] != NULL);
    int child_index = 0;
    for (int i = 0; i < 2; i++) {
        if (n->operans[i] != NULL) {
            child_index++;
            print_tree_ascii(n->operans[i], child_prefix,
                             child_index == child_count, FALSE);
        }
    }
}

void print_tree(node* n, int depth) { // verticale
    (void) depth;
    print_tree_ascii(n, "", TRUE, TRUE);
}

void push(stack** s, node* data) {
    stack* new_node = (stack*) malloc(sizeof(stack));
    if (!new_node) {
        perror("Errore malloc push stack\n");
        exit(1);
    }
    new_node->data = data;
    new_node->next = *s;
    *s = new_node;
}

node* pop(stack** s) {
    if (*s == NULL) {
        return NULL;
    }
    stack* next = (*s)->next;
    node* data = (*s)->data;
    free(*s);
    *s = next;
    return data;
}

void print_stack(stack* s) {
    printf("Stack: ");
    while (s != NULL) {
        if (s->data->isop) {
            switch (s->data->operation) {
                case NOT: printf("NOT "); break;
                case AND: printf("AND "); break;
                case OR: printf("OR "); break;
                case IMPLIES: printf("IMPLIES "); break;
                case IFF: printf("IFF "); break;
                case XOR: printf("XOR "); break;
            }
        } else if (s->data->isunaryop) {
            printf("Unary Operation: NOT ");
        } else {
            printf("Variable: %s (%s) ", s->data->var->name, s->data->var->value == TRUE ? "true" : "false");
        }
        s = s->next;
    }
    printf("\n");
}

stack* new_stack() {
    return NULL;
}

void append(coda** c, node* data) {
    coda* new_node = (coda*) malloc(sizeof(coda));
    if (!new_node) {
        perror("Errore malloc append coda\n");
        exit(1);
    }
    new_node->data = data;
    new_node->next = NULL;

    if (*c == NULL) {
        *c = new_node;
    } else {
        coda* temp = *c;
        while (temp->next != NULL) {
            temp = temp->next;
        }
        temp->next = new_node;
    }
}

void print_coda(coda* c) {
    printf("Coda: ");
    while (c != NULL) {
        if (c->data->isop) {
            printf("Op: ");
            switch (c->data->operation) {
                case NOT: printf("NOT"); break;
                case AND: printf("AND"); break;
                case OR: printf("OR"); break;
                case IMPLIES: printf("IMPLIES"); break;
                case IFF: printf("IFF"); break;
                case XOR: printf("XOR"); break;
            }
            printf(", ");
        } else if (c->data->isconstant) {
            printf("Const: %s ,", c->data->value == TRUE ? "true" : "false");
        } else {
            printf("Var: %s, ", c->data->var->name);
        }
        c = c->next;
    }
    printf("\n");
}

coda* new_coda() {
    return NULL;
}

char* preprocess_string(char* str) {
    char* new_str = (char*) malloc(MAX_STR_SIZE);
    if (!new_str) {
        perror("Errore malloc preprocess_string\n");
        exit(1);
    }
    new_str[0] = '\0';

    for (int i = 0; i < strlen(str); i++) {
        if (str[i] == '(' || str[i] == ')') {
            strncat(new_str, " ", 1);
            strncat(new_str, &str[i], 1);
            strncat(new_str, " ", 1);
        } else {
            strncat(new_str, &str[i], 1);
        }
    }

    strcpy(str, new_str);
    free(new_str);

    return str;
}


// esempio: var1 OR (var2 AND var3) -> var1 var2 var3 AND OR
//       or
//     /    \ 
// var1      and
//          /   \ 
//       var2   var3
void build_tree_from_postfix(tree** a) {
    printf("-- Costruzione albero --\n");

    stack* st = new_stack();

    coda* curr = (*a)->postfix;
    while (curr) {
        if (curr->data->isunaryop) {
            curr->data->operans[0] = pop(&st);
        } else if (curr->data->isop) {
            node* right = pop(&st);
            node* left = pop(&st);
            curr->data->operans[0] = left;
            curr->data->operans[1] = right;
        }
        push(&st, curr->data);
        curr = curr->next;
    }
    
    (*a)->root = pop(&st);

    //if stack is not empty, then there was an error in the postfix expression
    if (st != NULL) {
        fprintf(stderr, "Errore: espressione postfissa non valida\n");
        exit(1);
    }
}


// si costruisce l'albero partendo dalle foglie e risalendo fino alla radice
// left - root - right
// la root poi diventa il nuovo left 
//
// algoritmo Shunting-Yard
tree* parse(char* str) {
    stack* operatori = new_stack();
    coda* output = new_coda();
    tree* res_tree = new_tree();

    if (str == NULL || strlen(str) == 0) {
        perror("Stringa vuota");
        exit(1);
    }

    //preprocesso la stringa aggiundo lo spazio prima e dopo una parentesi
    str = preprocess_string(str);

    printf("Parsing string: %s\n", str);

    char* token = strtok(str, " ");
    while (token != NULL) {
        node* curr = NULL;

        // controllo se è un operatore logico
        if (strcmp(token, "OR") == 0 || strcmp(token, "or") == 0) {
            curr = new_node(TRUE, FALSE, FALSE, FALSE, &vOR);
        } else if (strcmp(token, "AND") == 0 || strcmp(token, "and") == 0) {
            curr = new_node(TRUE, FALSE, FALSE, FALSE, &vAND);
        } else if (strcmp(token, "NOT") == 0 || strcmp(token, "not") == 0) {
            curr = new_node(TRUE, TRUE, FALSE, FALSE, &vNOT);
        } else if (strcmp(token, "IMPLIES") == 0 || strcmp(token, "implies") == 0) {
            curr = new_node(TRUE, FALSE, FALSE, FALSE, &vIMPLIES);
        } else if (strcmp(token, "IFF") == 0 || strcmp(token, "iff") == 0) {
            curr = new_node(TRUE, FALSE, FALSE, FALSE, &vIFF);
        } else if (strcmp(token, "XOR") == 0 || strcmp(token, "xor") == 0) {
            curr = new_node(TRUE, FALSE, FALSE, FALSE, &vXOR);
        } else if (strcmp(token, "true") == 0) {
            accvalue true_value = TRUE;
            curr = new_node(FALSE, FALSE, TRUE, FALSE, &true_value);
        } else if (strcmp(token, "false") == 0) {
            accvalue false_value = FALSE;
            curr = new_node(FALSE, FALSE, TRUE, FALSE, &false_value);
        } else if (strcmp(token, "(") != 0 && strcmp(token, ")") != 0) {
            // assume it's a variable
            var* v = NULL;

            // check if variable already exists in the tree
            if (!varname_ckeck(res_tree->vars, res_tree->vars_count, token)) {
                v = new_var(token, FALSE);
                add_existing_var(res_tree, v);
            } else { // already exist need to be linked
                for (int i = 0; i < res_tree->vars_count; i++) {
                    if (strcmp(res_tree->vars[i]->name, token) == 0) {
                        v = res_tree->vars[i];
                        break;
                    }
                }
            }

            curr = new_node(FALSE, FALSE, FALSE, FALSE, v);
        }

        int isbrachet = FALSE;
        if (strcmp(token, "(") == 0) {
            curr = new_node(FALSE, FALSE, FALSE, TRUE, token);
            push(&operatori, curr);
            isbrachet = TRUE;
        } else if (strcmp(token, ")") == 0) {
            node* tmp = NULL;
            while (1) {
                tmp = pop(&operatori);

                if (tmp == NULL) {
                    fprintf(stderr, "Errore: parentesi non bilanciate\n");
                    exit(1);
                }
                if (tmp->isbracket) {
                    break; // found the matching '('
                }
                append(&output, tmp);
            }
            isbrachet = TRUE;
        }

        if(!isbrachet) {
            if (curr->isop || curr->isunaryop) {
                if (operatori != NULL) {
                    node* t = pop(&operatori);
                    if (t->isunaryop && !curr->isunaryop) {// devo controllare se sullo stack c'è un not e nel caso estrarlo e metterno in output
                        append(&output, t);
                    } else {
                        push(&operatori, t);
                    }
                }
                push(&operatori, curr); 
            } else if (curr->isconstant) {
                append(&output, curr);
            } else {
                append(&output, curr);
            }
        }

        token = strtok(NULL, " ");
    }

    node* tmp = NULL;
    while ((tmp = pop(&operatori)) != NULL) {
        append(&output, tmp);
    }

    printf("@@ Parsing completed ##\n");

    res_tree->postfix = output;

    // build the tree from the postfix notation
    build_tree_from_postfix(&res_tree);
    return res_tree;
}

void set_vars_values(tree *a, char* varname, accvalue newvalue) {
    for (int i=0; i<(a->vars_count); i++) {
        if(strcmp(a->vars[i]->name, varname) == 0) {
            a->vars[i]->value = newvalue;
            return;
        }
    }

    fprintf(stderr, "Errore set valore: variabile %s non trovata\n", varname);
    exit(1);
}

node* computeop(op operation, node* op1, node* op2) {
    if (op1 == NULL) {
        fprintf(stderr, "Errore: operando sinistro mancante\n");
        exit(1);
    }

    node* result = new_node(FALSE, FALSE, TRUE, FALSE, &vTRUE);

    accvalue op1value = op1->isconstant ? op1->value : op1->var->value;
    accvalue op2value = op2 != NULL && op2->isconstant ? op2->value : (op2 != NULL ? op2->var->value : FALSE);

    char* namevar1 = op1->isconstant ? "const" : op1->var->name;
    char* namevar2 = (op2 == NULL || op2->isconstant) ? "const" : op2->var->name;

    switch (operation) {
        case NOT:
            if (op2 != NULL) {
                fprintf(stderr, "Errore: NOT richiede un solo operando\n");
                exit(1);
            }
            result->value = !op1value;
            // printf("NOT: !%s (%s) --> %s\n", namevar1, op1value ? "true" : "false", result->value ? "true" : "false");
            break;
        case AND:
            if (op2 == NULL) {
                fprintf(stderr, "Errore: AND richiede due operandi\n");
                exit(1);
            }
            result->value = op1value && op2value;
            // printf("AND: %s (%s) && %s (%s) --> %s\n", namevar1, op1value ? "true" : "false", namevar2, op2value ? "true" : "false", result->value ? "true" : "false");
            break;
        case OR:
            if (op2 == NULL) {
                fprintf(stderr, "Errore: OR richiede due operandi\n");
                exit(1);
            }
            result->value = op1value || op2value;
            // printf("OR: %s (%s) || %s (%s) --> %s\n", namevar1, op1value ? "true" : "false", namevar2, op2value ? "true" : "false", result->value ? "true" : "false");
            break;
        case IMPLIES:
            if (op2 == NULL) {
                fprintf(stderr, "Errore: IMPLIES richiede due operandi\n");
                exit(1);
            }
            result->value = !op1value || op2value;
            // printf("IMPLIES: %s (%s) => %s (%s) --> %s\n", namevar1, op1value ? "true" : "false", namevar2, op2value ? "true" : "false", result->value ? "true" : "false");
            break;
        case IFF:
            if (op2 == NULL) {
                fprintf(stderr, "Errore: IFF richiede due operandi\n");
                exit(1);
            }
            result->value = (op1value && op2value) || (!op1value && !op2value);
            // printf("IFF: %s (%s) <=> %s (%s) --> %s\n", namevar1, op1value ? "true" : "false", namevar2, op2value ? "true" : "false", result->value ? "true" : "false");
            break;
        case XOR:
            if (op2 == NULL) {
                fprintf(stderr, "Errore: XOR richiede due operandi\n");
                exit(1);
            }
            result->value = (op1value && !op2value) || (!op1value && op2value);
            // printf("XOR: %s (%s) ^ %s (%s) --> %s\n", namevar1, op1value ? "true" : "false", namevar2, op2value ? "true" : "false", result->value ? "true" : "false");
            break;
        default:
            fprintf(stderr, "Errore: operazione logica non valida\n");
            exit(1);
    }
    return result;
}

// uso la rappresnetazione RPN per i calcoli, in futuro usero AST 
accvalue compute(tree *a) {
    // printf("\nComputing operation: \n");
    // printf("Coda: ");
    // for (coda* curr = a->postfix; curr != NULL; curr = curr->next) {
    //     if (curr->data->isop) {
    //         printf("Op: ");
    //         switch (curr->data->operation) {
    //             case NOT: printf("NOT"); break;
    //             case AND: printf("AND"); break;
    //             case OR: printf("OR"); break;
    //             case IMPLIES: printf("IMPLIES"); break;
    //             case IFF: printf("IFF"); break;
    //             case XOR: printf("XOR"); break;
    //         }
    //         printf(", ");
    //     } else if (curr->data->isconstant) {
    //         printf("Const: %s ,", curr->data->value == TRUE ? "true" : "false");
    //     } else {
    //         printf("Var: %s (%s), ", curr->data->var->name, curr->data->var->value == TRUE ? "true" : "false");
    //     }
    // }
    // printf("\n");

    stack* st = new_stack();

    coda* curr = a->postfix;
    while (curr) {
        node* result = NULL;
        if (curr->data->isunaryop) {
            node* operand = pop(&st);
            result = computeop(curr->data->operation, operand, NULL);
            push(&st, result);
        } else if (curr->data->isop) {
            node* right = pop(&st);
            node* left = pop(&st);
            result = computeop(curr->data->operation, left, right);
            push(&st, result);
        } else {
            push(&st, curr->data);
        }
        curr = curr->next;
    }

    node* final = pop(&st);
    if (final == NULL) {
        fprintf(stderr, "Errore: pila vuota durante il calcolo\n");
        exit(1);
    }

    return final->value;
}

// ritorna i valori (array) per ogni possibile combinazione in ordine
accvalue* gen_tabella_verita(tree *a) {
    // generiamo tutte le possibili combinazioni per le variabili

    accvalue* result = (accvalue*) malloc(sizeof(accvalue) * (int) pow(2, a->vars_count));
    if (!result) {
        perror("Errore malloc gen_tabella_verita\n");
        exit(1);
    }

    for (int j = 0; j < a->vars_count; j++) {
        printf("%s ",  a->vars[j]->name);
    }

    printf(" RES\n");

    for (int i = 0; i < pow(2, a->vars_count); i++) {
        int lcounter = i;
        for (int j = 0; j < a->vars_count; j++) {
            a->vars[j]->value = lcounter % 2;
            lcounter = (int) lcounter / 2;

            printf("%d ",  a->vars[j]->value);
        }

        result[i] = compute(a);

        printf(" %d\n", result[i]);
    }
    return result;
}

int compare_tabella_verita(accvalue* t1, accvalue* t2, int size) {
    for (int i = 0; i < size; i++) {
        if (t1[i] != t2[i]) {
            return 0; // not equivalent
        }
    }
    return 1; // equivalent
}

int main(int argc, char *argv[]) {
    tree* a;
    tree* b;

    char test1[MAX_STR_SIZE] = "not(B) OR C";
    char test2[MAX_STR_SIZE] = "not(C) OR B";
    // char test[MAX_STR_SIZE] = "NOT(A AND ( B OR C ))";
    // char test[MAX_STR_SIZE] = "NOT(NOT(var1) OR (var2 AND var3))";
    // char test[MAX_STR_SIZE] = "var1 AND var2 AND var3";
    // char test[MAX_STR_SIZE] = "(((A XOR B) AND (NOT C)) IFF (true IMPLIES (A OR false)))";

    a = parse(test1);
    b = parse(test2);
    print_tree(a->root, 0);
    print_vars_table(a);
    printf("\nSetting variable values...\n\n");
    // set_vars_values(a, "A", TRUE);
    set_vars_values(a, "B", TRUE);
    set_vars_values(a, "C", FALSE);
    print_vars_table(a);
    print_tree(a->root, 0);

    accvalue res = compute(a);
    printf("\nRisultato: %s\n", res ? "true": "false");

    accvalue* restabella1 = gen_tabella_verita(a);
    accvalue* restabella2 = gen_tabella_verita(b);

    if (compare_tabella_verita(restabella1, restabella2, (int) pow(2, a->vars_count))) {
        printf("Le due espressioni sono equivalenti.\n");
    } else {
        printf("Le due espressioni non sono equivalenti.\n");
    }

    return 0;
}