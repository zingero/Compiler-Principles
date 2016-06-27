/* debug_macros.h
 * GDB-Like information for debugging the compiler.
 *
 * Author: Ben Eyal
 */

#define TRANS(x, res) \
   (((x) == T_VOID)           ? snprintf(res, 16, "%s", "T_VOID")                     \
  : ((x) == T_NIL)            ? snprintf(res, 16, "%s", "T_NIL")                      \
  : ((x) == T_BOOL)           ? snprintf(res, 16, "%s", "T_BOOL")                     \
  : ((x) == T_CHAR)           ? snprintf(res, 16, "%s", "T_CHAR")                     \
  : ((x) == T_INTEGER)        ? snprintf(res, 16, "%s", "T_INTEGER")                  \
  : ((x) == T_STRING)         ? snprintf(res, 16, "%s", "T_STRING")                   \
  : ((x) == T_SYMBOL)         ? snprintf(res, 16, "%s", "T_SYMBOL")                   \
  : ((x) == T_PAIR)           ? snprintf(res, 16, "%s", "T_PAIR")                     \
  : ((x) == T_VECTOR)         ? snprintf(res, 16, "%s", "T_VECTOR")                   \
  : ((x) == T_CLOSURE)        ? snprintf(res, 16, "%s", "T_CLOSURE")                  \
  : ((x) == T_UNDEFINED)      ? snprintf(res, 16, "%s", "T_UNDEFINED")                \
  :                             snprintf(res, 16, "%ld", (x)))                        

#if DO_SHOW == 1 || DO_SHOW == 4
#define INFO {                                                                      \
  char type1[16], type2[16], type3[16], type4[16];                                  \
  printf("\n");                                                                     \
  int i;                                                                            \
  printf("----------------------------\n");                                         \
  printf("Memory Info:\n");                                                         \
  printf("----------------------------\n");                                         \
  for (i = 0; i <= IND(0); i += 4) {                                                \
    TRANS(IND(i), type1); TRANS(IND(i + 1), type2);                                 \
    TRANS(IND(i + 2) ,type3); TRANS(IND(i + 3), type4);                             \
    printf("MEM[%4d] = %-15s MEM[%4d] = %-15s MEM[%4d] = %-15s MEM[%4d] = %-15s\n", \
        i, type1,                                                                   \
        i + 1, type2,                                                               \
        i + 2, type3,                                                               \
        i + 3, type4);                                                              \
  }                                                                                 \
  printf("\n");                                                                     \
  printf("----------------------------\n");                                         \
  printf("Register Info:\n");                                                       \
  printf("----------------------------\n");                                         \
  printf("FP = %-10ld SP = %ld\n\n", FP, SP);                                       \
  TRANS(R0, type1); TRANS(R1, type2);                                               \
  printf("R0 = %-10s R1 = %s\n", type1, type2);                                     \
  TRANS(R2, type1); TRANS(R3, type2);                                               \
  printf("R2 = %-10s R3 = %s\n", type1, type2);                                     \
  TRANS(R4, type1); TRANS(R5, type2);                                               \
  printf("R4 = %-10s R5 = %s\n", type1, type2);                                   \
  TRANS(R6, type1); TRANS(R7, type2);                                               \
  printf("R6 = %-10s R7 = %s\n", type1, type2);                                   \
  TRANS(R8, type1); TRANS(R9, type2);                                               \
  printf("R8 = %-10s R9 = %s\n\n", type1, type2);                                   \
  printf("----------------------------\n");                                         \
  printf("Stack Info:\n");                                                          \
  printf("----------------------------\n");                                         \
  for (i = SP - 1; i >= 0; i--) {                                                   \
    TRANS(STACK(i), type1);                                                         \
    printf("STACK[%2d] = %s\n", i, type1);                                          \
  }                                                                                 \
  printf("\n");                                                                     \
}

#define STK {                                                                       \
  printf("----------------------------\n");                                         \
  printf("Stack Info:\n");                                                          \
  printf("----------------------------\n");                                         \
  char type1[16];                                                                   \
  int i;                                                                            \
  for (i = SP - 1; i >= 0; i--) {                                                   \
    TRANS(STACK(i), type1);                                                         \
    printf("STACK[%2d] = %s\n", i, type1);                                          \
  }                                                                                 \
  printf("\n");                                                                     \
}

#define REG {                                                                       \
  char type1[16], type2[16];                                                        \
  printf("----------------------------\n");                                         \
  printf("Register Info:\n");                                                       \
  printf("----------------------------\n");                                         \
  printf("FP = %-10ld SP = %ld\n\n", FP, SP);                                       \
  TRANS(R0, type1); TRANS(R1, type2);                                               \
  printf("R0 = %-10s R1 = %s\n", type1, type2);                                     \
  TRANS(R2, type1); TRANS(R3, type2);                                               \
  printf("R2 = %-10s R3 = %s\n", type1, type2);                                     \
  TRANS(R4, type1); TRANS(R5, type2);                                               \
  printf("R4 = %-10s R5 = %s\n\n", type1, type2);                                   \
}

#define BP { INFO; getchar(); }
#else
#define INFO {}
#define STK {}
#define REG {}
#define BP {}
#endif