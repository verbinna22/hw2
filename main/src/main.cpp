/* Lama SM Bytecode interpreter */

#include <algorithm>
#include <bits/types/clockid_t.h>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <stdint.h>
extern "C" {
#define _Noreturn [[noreturn]]
#include "runtime/gc.h"
#include "runtime/runtime_common.h"
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include "runtime/runtime.h"

void *__start_custom_data;
void *__stop_custom_data;

extern void *Bstring (aint* args/*void *p*/);
extern void *Bsexp (aint* args, aint bn);
extern void *Bsta (void *x, aint i, void *v);
extern void *Belem (void *p, aint i);
extern void *Bclosure (aint* args, aint bn);
extern aint Btag (void *d, aint t, aint n);
extern aint Barray_patt (void *d, aint n);
extern void Bmatch_failure (void *v, char *fname, aint line, aint col);
extern aint Bboxed_patt (void *x);
extern aint Bunboxed_patt (void *x);
extern aint Bstring_patt (void *x, void *y);
extern aint Bstring_tag_patt (void *x);
extern aint Barray_tag_patt (void *x);
extern aint Bsexp_tag_patt (void *x);
extern aint Bclosure_tag_patt (void *x);
extern aint Lread ();
extern aint Lwrite (aint n);
extern aint Llength (void *p);
extern void *Lstring (aint* args /* void *p */);
extern void *Barray (aint* args, aint bn);
extern aint LtagHash (char *s);
extern size_t __gc_stack_top, __gc_stack_bottom;
void dump_heap ();
}

/* The unpacked representation of bytecode file */
typedef struct
{
  char *string_ptr;          /* A pointer to the beginning of the string table */
  int *public_ptr;           /* A pointer to the beginning of publics table    */
  char *code_ptr;            /* A pointer to the bytecode itself               */
  int *global_ptr;           /* A pointer to the global area                   */
  int stringtab_size;        /* The size (in bytes) of the string table        */
  int global_area_size;      /* The size (in words) of global area             */
  int public_symbols_number; /* The number of public symbols                   */
  char buffer[0];
} bytefile;

/* Gets a string from a string table by an index */
char *get_string(bytefile *f, int pos)
{
  return &f->string_ptr[pos];
}

/* Gets a name for a public symbol */
char *get_public_name(bytefile *f, int i)
{
  return get_string(f, f->public_ptr[i * 2]);
}

/* Gets an offset for a publie symbol */
int get_public_offset(bytefile *f, int i)
{
  return f->public_ptr[i * 2 + 1];
}

/* Reads a binary bytecode file by name and unpacks it */
bytefile *read_file(char *fname)
{
  FILE *f = fopen(fname, "rb");
  long size;
  bytefile *file;

  if (f == 0)
  {
    failure("%s\n", strerror(errno));
  }

  if (fseek(f, 0, SEEK_END) == -1)
  {
    failure("%s\n", strerror(errno));
  }

  file = (bytefile *)malloc(sizeof(void *) * 4 + (size = ftell(f)));

  if (file == 0)
  {
    failure("*** FAILURE: unable to allocate memory.\n");
  }

  rewind(f);

  if (size != fread(&file->stringtab_size, 1, size, f))
  {
    failure("%s\n", strerror(errno));
  }

  fclose(f);

  file->string_ptr = &file->buffer[file->public_symbols_number * 2 * sizeof(int)];
  file->public_ptr = (int *)file->buffer;
  file->code_ptr = &file->string_ptr[file->stringtab_size];
  file->global_ptr = (int *)malloc(file->global_area_size * sizeof(int));

  return file;
}

/* Disassembles the bytecode pool */
void disassemble(FILE *f, bytefile *bf)
{

#define INT (ip += sizeof(int), *(int *)(ip - sizeof(int)))
#define BYTE *ip++
#define STRING get_string(bf, INT)
#define FAIL failure("ERROR: invalid opcode %d-%d\n", h, l)

  char *ip = bf->code_ptr;
  char *ops[] = {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  char *pats[] = {"=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun"};
  char *lds[] = {"LD", "LDA", "ST"};
  do
  {
    char x = BYTE,
         h = (x & 0xF0) >> 4,
         l = x & 0x0F;

    fprintf(f, "0x%.8x:\t", ip - bf->code_ptr - 1);

    switch (h)
    {
    case 15:
      goto stop;

    /* BINOP */
    case 0:
      fprintf(f, "BINOP\t%s", ops[l - 1]);
      break;

    case 1:
      switch (l)
      {
      case 0:
        fprintf(f, "CONST\t%d", INT);
        break;

      case 1:
        fprintf(f, "STRING\t%s", STRING);
        break;

      case 2:
        fprintf(f, "SEXP\t%s ", STRING);
        fprintf(f, "%d", INT);
        break;

      case 3:
        fprintf(f, "STI");
        break;

      case 4:
        fprintf(f, "STA");
        break;

      case 5:
        fprintf(f, "JMP\t0x%.8x", INT);
        break;

      case 6:
        fprintf(f, "END");
        break;

      case 7:
        fprintf(f, "RET");
        break;

      case 8:
        fprintf(f, "DROP");
        break;

      case 9:
        fprintf(f, "DUP");
        break;

      case 10:
        fprintf(f, "SWAP");
        break;

      case 11:
        fprintf(f, "ELEM");
        break;

      default:
        FAIL;
      }
      break;

    case 2:
    case 3:
    case 4:
      fprintf(f, "%s\t", lds[h - 2]);
      switch (l)
      {
      case 0:
        fprintf(f, "G(%d)", INT);
        break;
      case 1:
        fprintf(f, "L(%d)", INT);
        break;
      case 2:
        fprintf(f, "A(%d)", INT);
        break;
      case 3:
        fprintf(f, "C(%d)", INT);
        break;
      default:
        FAIL;
      }
      break;

    case 5:
      switch (l)
      {
      case 0:
        fprintf(f, "CJMPz\t0x%.8x", INT);
        break;

      case 1:
        fprintf(f, "CJMPnz\t0x%.8x", INT);
        break;

      case 2:
        fprintf(f, "BEGIN\t%d ", INT);
        fprintf(f, "%d", INT);
        break;

      case 3:
        fprintf(f, "CBEGIN\t%d ", INT);
        fprintf(f, "%d", INT);
        break;

      case 4:
        fprintf(f, "CLOSURE\t0x%.8x", INT);
        {
          int n = INT;
          for (int i = 0; i < n; i++)
          {
            switch (BYTE)
            {
            case 0:
              fprintf(f, "G(%d)", INT);
              break;
            case 1:
              fprintf(f, "L(%d)", INT);
              break;
            case 2:
              fprintf(f, "A(%d)", INT);
              break;
            case 3:
              fprintf(f, "C(%d)", INT);
              break;
            default:
              FAIL;
            }
          }
        };
        break;

      case 5:
        fprintf(f, "CALLC\t%d", INT);
        break;

      case 6:
        fprintf(f, "CALL\t0x%.8x ", INT);
        fprintf(f, "%d", INT);
        break;

      case 7:
        fprintf(f, "TAG\t%s ", STRING);
        fprintf(f, "%d", INT);
        break;

      case 8:
        fprintf(f, "ARRAY\t%d", INT);
        break;

      case 9:
        fprintf(f, "FAIL\t%d", INT);
        fprintf(f, "%d", INT);
        break;

      case 10:
        fprintf(f, "LINE\t%d", INT);
        break;

      default:
        FAIL;
      }
      break;

    case 6:
      fprintf(f, "PATT\t%s", pats[l]);
      break;

    case 7:
    {
      switch (l)
      {
      case 0:
        fprintf(f, "CALL\tLread");
        break;

      case 1:
        fprintf(f, "CALL\tLwrite");
        break;

      case 2:
        fprintf(f, "CALL\tLlength");
        break;

      case 3:
        fprintf(f, "CALL\tLstring");
        break;

      case 4:
        fprintf(f, "CALL\tBarray\t%d", INT);
        break;

      default:
        FAIL;
      }
    }
    break;

    default:
      FAIL;
    }

    fprintf(f, "\n");
  } while (1);
stop:
  fprintf(f, "<end>\n");
}

#define debug(...) //fprintf(__VA_ARGS__)
constexpr uint64_t OPERAND_STACK_SIZE_U = 1024 * 1024;
constexpr uint64_t CALL_STACK_SIZE_U = 1024 * 1024;

uint64_t memory_to_simulation[1 + OPERAND_STACK_SIZE_U + CALL_STACK_SIZE_U];

uint64_t *OPERAND_STACK_SIZE_BEGIN = memory_to_simulation + 1;
uint64_t *OPERAND_STACK_SIZE_END = memory_to_simulation + 1 + OPERAND_STACK_SIZE_U;
constexpr uint64_t *CALL_STACK_SIZE_BEGIN = memory_to_simulation + 1 + OPERAND_STACK_SIZE_U;
constexpr uint64_t *CALL_STACK_SIZE_END = memory_to_simulation + 1 + OPERAND_STACK_SIZE_U + CALL_STACK_SIZE_U;
uint64_t *operand_stack_end = OPERAND_STACK_SIZE_BEGIN;
uint64_t *fp = CALL_STACK_SIZE_BEGIN + 2;
uint64_t *sp = CALL_STACK_SIZE_BEGIN + 5;

bytefile *file;
uint main_ptr;

void move_globals(uint64_t nglobals) {
  OPERAND_STACK_SIZE_BEGIN += nglobals;
  fp += nglobals;
  sp += nglobals;
  operand_stack_end += nglobals;
}

uint64_t *get_global(uint64_t i) {
  return (OPERAND_STACK_SIZE_BEGIN - i - 1);//file->global_ptr + i;
}

uint64_t pop_operand() {
  if (operand_stack_end == OPERAND_STACK_SIZE_BEGIN) {
    throw std::logic_error("op stack underflow"); // TODO overflow
  }
  --operand_stack_end;
  uint64_t result = *operand_stack_end;
  *operand_stack_end = 0;
  return result;
}

void push_operand(uint64_t operand) {
  *operand_stack_end = operand;
  ++operand_stack_end; 
  if (operand_stack_end >= OPERAND_STACK_SIZE_END) {
    throw std::logic_error("op stack overflow"); // TODO overflow
  }
}

void call_begin(uint64_t nargs, char *next) {
  for (int i = 0; i < nargs; ++i) {
    sp[i] = pop_operand();
  }
  sp[nargs] = reinterpret_cast<uint64_t>(next);
  sp[nargs + 1] = reinterpret_cast<uint64_t>(sp);
  sp[nargs + 2] = reinterpret_cast<uint64_t>(fp);
  fp = &sp[nargs];
  sp += (nargs + 3);
  if (sp >= CALL_STACK_SIZE_END) {
    throw std::logic_error("call stack overflow"); // TODO overflow
  }
}

void alloc_locals(uint64_t nlocals) {
  sp += nlocals;
  debug(stderr, "\nalloc locals:\t%lu\n", nlocals);
  if (sp >= CALL_STACK_SIZE_END) {
    throw std::logic_error("call stack overflow"); // TODO overflow
  }
}

uint64_t *get_local(uint64_t i) {
  debug(stderr, "\tget local:%li sp%x osb%x\n", *(sp - i - 1), sp, OPERAND_STACK_SIZE_BEGIN);
  return (sp - i - 1);
}

void print_stacks() { // TODO
  debug(stderr, "\n\nstack:");
  for (uint64_t *i = operand_stack_end - 1; i >= OPERAND_STACK_SIZE_BEGIN; --i) {
    debug(stderr, " %li ", *i);
  }

  debug(stderr, "\n\ngloba + clos:");
  for (uint64_t *i = OPERAND_STACK_SIZE_BEGIN - 1; i >= memory_to_simulation; --i) {
    debug(stderr, " %li ", *i);
  }

  debug(stderr, "\n\ncall stack:");
  for (uint64_t *i = sp - 1; i >= CALL_STACK_SIZE_BEGIN; --i) {
    debug(stderr, " %li (%lx) ", *i, *i);
  }
  debug(stderr, "\n\n");
}

uint64_t *get_arg(uint64_t i) {
  return (fp - i - 1);
}

uint64_t *closure_address = memory_to_simulation;

uint64_t *get_closure(uint64_t i) {
  return reinterpret_cast<uint64_t *>(*closure_address) + (i + 1); //  Value.Access i -> I (word_size * (i + 1), r15)
}

char *file_name;
char *chars = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'";

uint64_t hash_tag(char *tag) {
  // method hash tag =
  //     let h = Stdlib.ref 0 in
  //     for i = 0 to min (String.length tag - 1) 9 do
  //       h := (!h lsl 6) lor String.index chars tag.[i]
  //     done;
  uint64_t h = 0;
  uint64_t length = std::min<uint64_t>(std::strlen(tag), 10);
  for (int i = 0; i < length; ++i) {
    uint64_t index = std::strchr(chars, tag[i]) - chars;
    h = (h << 6) | index;
  }
  return h;
}

char *call_end() {
  char *result = reinterpret_cast<char *>(fp[0]);
  uint64_t *need_sp = reinterpret_cast<uint64_t *>(fp[1]);
  fp = reinterpret_cast<uint64_t *>(fp[2]);
  while (sp > need_sp) {
    --sp;
    *sp = 0;
  }
  return result;
}

uint64_t make_boxed(uint64_t n) {
  return (n << 1) + 1;
}

uint64_t make_unboxed(int64_t n) {
  return n >> 1;
}

/* Disassembles the bytecode pool */
void run_interpreter(bytefile *bf, FILE *f = stderr)
{

#define INT (ip += sizeof(int), *(int *)(ip - sizeof(int)))
#define BYTE *ip++
#define STRING get_string(bf, INT)
#define FAIL failure("ERROR: invalid opcode %d-%d\n", h, l)

  char *ip = main_ptr + bf->code_ptr;
  char *ops[] = {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  char *pats[] = {"=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun"};
  char *lds[] = {"LD", "LDA", "ST"};
  __gc_init();
  __gc_stack_bottom = reinterpret_cast<size_t>(memory_to_simulation + sizeof(memory_to_simulation) / sizeof(memory_to_simulation[0]) - sizeof(void *));
  __gc_stack_top = (reinterpret_cast<size_t>(memory_to_simulation) - sizeof(void *)) & (~0xFull);
  move_globals(bf->global_area_size);
  // begin simulation jump to main
  do
  {
    char x = BYTE,
         h = (x & 0xF0) >> 4,
         l = x & 0x0F;
// TODO: no debug mode (gc), additional fun to print bc, check
    //dump_heap(); // TODO
    debug(f, "0x%.8x (0x%.8x):\t", ip - bf->code_ptr - 1, ip - 1);
    print_stacks();

    switch (h)
    {
    case 15:
      goto stop; // stop execution

    /* BINOP  must be valid*/
    case 0: {
      debug(f, "BINOP\t%s", ops[l - 1]); // TODO
      uint64_t result;
      uint64_t first = make_unboxed(pop_operand());
      uint64_t second = make_unboxed(pop_operand());
      debug(stderr, "%li %li %li\n", int64_t(second), int64_t(first), int64_t(second) > int64_t(first));
      switch (l) {
        case 1: result = second + first; break;
        case 2: result = second - first; break;
        case 3: result = int64_t(second) * int64_t(first); break;
        case 4:
          if (first == 0) {
            debug(stderr, "Error: divide by zero");
            return;
          }
          result = int64_t(second) / int64_t(first); break;
        case 5:
          if (first == 0) {
            debug(stderr, "Error: divide by zero");
            return;
          }
          result = int64_t(second) % int64_t(first); break;
        case 6: result = int64_t(second) < int64_t(first); break;
        case 7: result = int64_t(second) <= int64_t(first); break;
        case 8: result = int64_t(second) > int64_t(first); break;
        case 9: result = int64_t(second) >= int64_t(first); break;
        case 10: result = (second == first); break;
        case 11: result = (second != first); break;
        case 12: result = (second && first); break;
        case 13: result = (second || first); break;
      }
      push_operand((result << 1) + 1);
      break;
    }

    case 1:
      switch (l)
      {
      case 0: {
        uint64_t n = INT;
        debug(f, "CONST\t%d", n); // TODO
        push_operand(make_boxed(n));
        break;
      }

      case 1: {
        uint64_t ptr = reinterpret_cast<uint64_t>(STRING);
        debug(f, "STRING\t%s", ptr); // TODO
        uint64_t allocated_ptr = reinterpret_cast<uint64_t>(Bstring(reinterpret_cast<aint *>(&ptr)));
        push_operand(allocated_ptr);
        break;
      }

      case 2: {
        uint64_t ptr = reinterpret_cast<uint64_t>(STRING);
        uint64_t n = INT;
        debug(f, "SEXP\t%s ", ptr);  // TODO
        debug(f, "%d", n);
        aint tmp_array[n + 1];
        tmp_array[n] = LtagHash(reinterpret_cast<char *>(ptr));
        for (int i = n - 1; i >= 0; --i) {
          tmp_array[i] = pop_operand();
        }
        uint64_t allocated_value = reinterpret_cast<uint64_t>(Bsexp(tmp_array, static_cast<aint>(make_boxed(n + 1))));
        push_operand(allocated_value);
        break;
      }

      case 3:
        throw std::logic_error("STI temporary prohibited");
        break;

      case 4: {
        debug(f, "STA");  // TODO
        uint64_t v = pop_operand();
        uint64_t i = pop_operand();
        uint64_t y = pop_operand();
        push_operand(reinterpret_cast<uint64_t>(Bsta(reinterpret_cast<void *>(y), static_cast<aint>(i), reinterpret_cast<void *>(v))));
        break;
      }

      case 5: {
        uint64_t addr = INT;
        debug(f, "JMP\t0x%.8x", addr); // TODO
        ip = addr + bf->code_ptr;
        break;
      }

      case 6:
        debug(f, "END"); // TODO
        ip = call_end();
        break;

      case 7:
        debug(f, "RET"); // TODO
        ip = call_end();
        break;

      case 8:
        debug(f, "DROP");  // TODO
        pop_operand();
        break;

      case 9: {
        debug(f, "DUP");  // TODO
        uint64_t value = pop_operand();
        push_operand(value);
        push_operand(value);
        break;
      }

      case 10: {
        debug(f, "SWAP"); // TODO
        uint64_t first = pop_operand();
        uint64_t second = pop_operand();
        push_operand(first);
        push_operand(second);
        break;
      }

      case 11: {
        debug(f, "ELEM"); // TODO
        uint64_t i = pop_operand();
        uint64_t p = pop_operand();
        push_operand(reinterpret_cast<uint64_t>(Belem(reinterpret_cast<void *>(p), static_cast<aint>(i))));
        break;
      }

      default:
        FAIL; // TODO: another check
      }
      break;

    case 2: {// LD
      debug(f, "%s\t", lds[h - 2]);
      uint64_t variable;
      uint64_t i = INT;
      switch (l)
      {
      case 0:
        debug(f, "G(%d)", i);
        variable = *get_global(i);
        debug(stderr, "%li\t", variable);
        break;
      case 1:
        debug(f, "L(%d)", i);
        variable = *get_local(i);
        debug(stderr, "%li\t", variable);
        break;
      case 2:
        debug(f, "A(%d)", i);
        variable = *get_arg(i);
        break;
      case 3:
        debug(f, "C(%d)", i);
        variable = *get_closure(i);
        break;
      default:
        FAIL;
      }
      push_operand(variable);
      break;
    }
    case 3: // LDA
      throw std::logic_error("LDA temporary prohibited");
    case 4: {// ST
      debug(f, "%s\t", lds[h - 2]); // TODO
      uint64_t i = INT;
      switch (l)
      {
      case 0: {
        debug(f, "G(%d)", i);
        uint64_t value = pop_operand();
        push_operand(value);
        debug(stderr, "%li\t", value);
        *get_global(i) = value;
        break;
      }
      case 1: {
        debug(f, "L(%d)", i);
        uint64_t value = pop_operand();
        push_operand(value);
        debug(stderr, "%li\t", value);
        *get_local(i) = value;
        break;
      }
      case 2: {
        debug(f, "A(%d)", i);
        uint64_t value = pop_operand();
        push_operand(value);
        *get_arg(i) = value;
        break;
      }
      case 3: {
        debug(f, "C(%d)", i);
        uint64_t value = pop_operand();
        push_operand(value);
        *get_closure(i) = value;
        break;
      }
      default:
        FAIL;
      }
      break;
    }

    case 5:
      switch (l)
      {
      case 0: {
        uint64_t addr = INT;
        debug(f, "CJMPz\t0x%.8x", addr); // TODO
        uint64_t value = make_unboxed(pop_operand());
        if (value == 0) {
          ip = addr + bf->code_ptr;
        }
        break;
      }

      case 1: {
        uint64_t addr = INT;
        debug(f, "CJMPnz\t0x%.8x", addr); // TODO
        uint64_t value = make_unboxed(pop_operand());
        debug(stderr, "%li\n", int64_t(value));
        if (value != 0) {
          ip = addr + bf->code_ptr;
        }
        break;
      }

      case 2: {
        uint64_t nargs = INT;
        uint64_t nlocals = INT;
        debug(f, "BEGIN\t%d ", nargs); // TODO
        debug(f, "%d", nlocals);
        alloc_locals(nlocals);
        break;
      }

      case 3: {
        uint64_t nargs = INT;
        uint64_t nlocals = INT;
        debug(f, "CBEGIN\t%d ", nargs);
        debug(f, "%d", nlocals);
        alloc_locals(nlocals);
        break;
      }

      case 4: {
        uint64_t addr = INT;
        debug(f, "CLOSURE\t0x%.8x", addr); // TODO
          int n = INT;
          aint args[n + 1];
          {
          args[0] = addr;
          for (int i = 0; i < n; i++)
          {
            switch (BYTE)
            {
            case 0: {
              uint64_t j = INT;
              debug(f, "G(%d)", j);
              args[i + 1] = *get_global(j);
              break;
            }
            case 1: {
              uint64_t j = INT;
              debug(f, "L(%d)", j);
              args[i + 1] = *get_local(j);
              break;
            }
            case 2: {
              uint64_t j = INT;
              debug(f, "A(%d)", j);
              args[i + 1] = *get_arg(j);
              break;
            }
            case 3: {
              uint64_t j = INT;
              debug(f, "C(%d)", j);
              args[i + 1] = *get_closure(j);
              break;
            }
            default:
              FAIL;
            }
          }
        };
        push_operand(reinterpret_cast<uint64_t>(Bclosure(args, make_boxed(n))));
        break;
      }

      case 5: {
        uint64_t args_number = INT;
        debug(f, "CALLC\t%d", args_number);
        call_begin(args_number, ip);
        *closure_address = pop_operand();
        ip = *reinterpret_cast<uint64_t *>(*closure_address) + bf->code_ptr;
        break;
      }

      case 6: {
        uint64_t addr = INT;
        uint64_t args_number = INT;
        debug(f, "CALL\t0x%.8x ", addr); // TODO
        debug(f, "%d", args_number);
        call_begin(args_number, ip);
        ip = addr + bf->code_ptr;
        break;
      }

      case 7: {
        uint64_t string_ptr = reinterpret_cast<uint64_t>(STRING);
        uint64_t size = INT;
        debug(f, "TAG\t%s ", string_ptr);
        debug(f, "%d", size); // TODO
        uint64_t data = pop_operand();
        uint64_t value = Btag(
          reinterpret_cast<char *>(data), LtagHash(reinterpret_cast<char *>(string_ptr)), make_boxed(size));
        push_operand(value);
        break;
      }

      case 8: {
        uint64_t size = INT;
        debug(f, "ARRAY\t%d", size); // TODO
        uint64_t data = pop_operand();
        uint64_t value = Barray_patt(reinterpret_cast<void *>(data), make_boxed(size));
        push_operand(value);
        break;
      }

      case 9: {
        uint64_t line = INT;
        uint64_t column = INT;
        debug(f, "FAIL\t%d", line);
        debug(f, "%d", column);
        uint64_t data = pop_operand();
        push_operand(data); // TODO eliminate
        Bmatch_failure(reinterpret_cast<void *>(data), file_name, line, column);
        break;
      }

      case 10: {
        uint64_t n = INT;
        debug(f, "LINE\t%d", n);
        break;
      }

      default:
        FAIL; // TODO remove
      }
      break;

    case 6: {
      debug(f, "PATT\t%s", pats[l]);
      switch (l) {
        case 0: {// strcmp
          void *first = reinterpret_cast<void *>(pop_operand());
          void *second = reinterpret_cast<void *>(pop_operand());
          push_operand(Bstring_patt(first, second));
          break;
        }
        case 1: // string
          push_operand(Bstring_tag_patt(reinterpret_cast<void *>(pop_operand())));
          break;
        case 2: // array
          push_operand(Barray_tag_patt(reinterpret_cast<void *>(pop_operand())));
          break;
        case 3: // sexp
          push_operand(Bsexp_tag_patt(reinterpret_cast<void *>(pop_operand())));
          break;
        case 4: // ref = boxed
          push_operand(Bboxed_patt(reinterpret_cast<void *>(pop_operand())));
          break;
        case 5: // val = unboxed
          push_operand(Bunboxed_patt(reinterpret_cast<void *>(pop_operand())));
          break;
        case 6: // fun
          push_operand(Bclosure_tag_patt(reinterpret_cast<void *>(pop_operand())));
          break;
      }
      break;
    }

    case 7:
    { // TODO
      switch (l)
      {
      case 0:
        debug(f, "CALL\tLread");
        fprintf(stdout, " ");
        push_operand(Lread());
        break;

      case 1:
        debug(f, "CALL\tLwrite");
        Lwrite(pop_operand());
        push_operand(0);
        break;

      case 2:
        debug(f, "CALL\tLlength");
        push_operand(Llength(reinterpret_cast<void *>(pop_operand())));
        break;

      case 3: {
        debug(f, "CALL\tLstring");
        uint64_t value = pop_operand();
        push_operand(reinterpret_cast<uint64_t>(Lstring(reinterpret_cast<aint *>(&value))));
        break;
      }

      case 4: {
        uint64_t n = INT;
        debug(f, "CALL\tBarray\t%d", n);
        aint args[n];
        for (int i = n - 1; i >= 0; --i) {
          args[i] = pop_operand();
        }
        push_operand(reinterpret_cast<uint64_t>(Barray(args, make_boxed(n))));
        break;
      }

      default:
        FAIL; // TODO
      }
    }
    break;

    default:
      FAIL; // TODO
    }

    debug(f, "\n");
  } while (sp != nullptr);
stop:
  debug(f, "<end>\n");
  __shutdown();
}

/* Dumps the contents of the file */
void dump_file(FILE *f, bytefile *bf)
{
  int i;

  debug(f, "String table size       : %d\n", bf->stringtab_size);
  debug(f, "Global area size        : %d\n", bf->global_area_size);
  debug(f, "Number of public symbols: %d\n", bf->public_symbols_number);
  debug(f, "Public symbols          :\n");

  bool found = false;
  for (i = 0; i < bf->public_symbols_number; i++) {
    char *name =  get_public_name(bf, i);
    uint64_t offset = get_public_offset(bf, i);
    debug(f, "   0x%.8x: %s\n", offset, name);
    if (std::strcmp(name, "main") == 0) {
      main_ptr = (offset);
      found = true;
      break;
    }
  }

  debug(f, "Code:\n");
  if (!found) {
    fprintf(stderr, "No main");
    return;
  }
  run_interpreter(bf);
}

int main(int argc, char *argv[])
{
  file_name = argv[1];
  bytefile *f = read_file(file_name);
  file = f;
  dump_file(stderr, f);
  return 0;
}
