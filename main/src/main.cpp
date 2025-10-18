/* Lama SM Bytecode interpreter */

#include <bits/types/clockid_t.h>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <stdint.h>
#include <unordered_map>
#include <unordered_set>

extern "C" {
#define _Noreturn [[noreturn]]
#include "runtime/gc.h"
#include "runtime/runtime_common.h"
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include "runtime/runtime.h"

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
void dump_heap ();

extern size_t __gc_stack_top, __gc_stack_bottom;
}

/* The unpacked representation of bytecode file */
typedef struct
{
  const char *string_ptr;          /* A pointer to the beginning of the string table */
  const int *public_ptr;           /* A pointer to the beginning of publics table    */
  const char *code_ptr;            /* A pointer to the bytecode itself               */
  const int *global_ptr;           /* A pointer to the global area                   */
  int stringtab_size;        /* The size (in bytes) of the string table        */
  int global_area_size;      /* The size (in words) of global area             */
  int public_symbols_number; /* The number of public symbols                   */
  const char buffer[0];
} bytefile;

static size_t bytefile_size;
static const bytefile *file;
static const char *file_name;

/* Gets a string from a string table by an index */
static inline const char *get_string(const bytefile *f, int pos)
{
  [[unlikely]] if (pos >= f->stringtab_size) {
    throw std::logic_error("incorrect string offset");
  }
  const char *string = &f->string_ptr[pos];
  return string;
}

/* Gets a name for a public symbol */
static inline const char *get_public_name(const bytefile *f, int i)
{
  return get_string(f, f->public_ptr[i * 2]);
}

/* Gets an offset for a publie symbol */
static inline int get_public_offset(const bytefile *f, int i)
{
  return f->public_ptr[i * 2 + 1];
}

/* Reads a binary bytecode file by name and unpacks it */
static const bytefile *read_file(const char *fname)
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

  bytefile_size = sizeof(void *) * 4 + (size = ftell(f));
  file = (bytefile *)malloc(bytefile_size);

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
  file->global_ptr = nullptr;

  if (file->string_ptr >= (char *)file + bytefile_size ||
    (char *)file->public_ptr >= (char *)file + bytefile_size ||
    file->code_ptr >= (char *)file + bytefile_size ||
    file->string_ptr + file->stringtab_size > (char *)file + bytefile_size ||
    file->stringtab_size > bytefile_size
  ) {
    throw std::logic_error("bad file format");
  }

  if (file->stringtab_size > 0 && file->string_ptr[file->stringtab_size - 1] != 0) {
    throw std::logic_error("string is not in file");
  }

  return file;
}

#define INT (ip += sizeof(int), *(int *)(ip - sizeof(int)))
#define BYTE *ip++
#define STRING get_string(file, INT)
#define FAIL failure("ERROR: invalid opcode %d-%d\n", h, l)

static void print_code(char *ip, FILE *f = stderr)
{
  const char *ops[] = {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  const char *pats[] = {"=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun"};
  const char *lds[] = {"LD", "LDA", "ST"};
  
    char x = BYTE,
         h = (x & 0xF0) >> 4,
         l = x & 0x0F;

    fprintf(f, "0x%.8x:\t", ip - file->code_ptr - 1);

    switch (h)
    {
    case 15:
      fprintf(f, "<end>");
      break;

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
}

constexpr uint64_t OPERAND_STACK_SIZE_U = 1024 * 1024;
constexpr uint64_t CALL_STACK_SIZE_U = 1024 * 1024;
constexpr uint64_t ALIGNMENT_FEATURE = 16;

static uint64_t memory_to_simulation[1 + ALIGNMENT_FEATURE + OPERAND_STACK_SIZE_U + CALL_STACK_SIZE_U];

static uint64_t *OPERAND_STACK_SIZE_BEGIN = memory_to_simulation + 1 + ALIGNMENT_FEATURE;
static uint64_t *OPERAND_STACK_SIZE_END = memory_to_simulation + 1 + ALIGNMENT_FEATURE + OPERAND_STACK_SIZE_U;
constexpr uint64_t *CALL_STACK_SIZE_BEGIN = memory_to_simulation + 1 + ALIGNMENT_FEATURE + OPERAND_STACK_SIZE_U;
constexpr uint64_t *CALL_STACK_SIZE_END = memory_to_simulation + 1 + ALIGNMENT_FEATURE + OPERAND_STACK_SIZE_U + CALL_STACK_SIZE_U;
static uint64_t *operand_stack_end = OPERAND_STACK_SIZE_BEGIN;
static uint64_t *fp = CALL_STACK_SIZE_BEGIN + 2;
static uint64_t *sp = CALL_STACK_SIZE_BEGIN + 2 + 4;
static uint64_t main_ptr;
static uint64_t *closure_address = memory_to_simulation + ALIGNMENT_FEATURE;

static inline void move_globals(uint64_t nglobals) {
  OPERAND_STACK_SIZE_BEGIN += nglobals;
  fp += nglobals;
  sp += nglobals;
  operand_stack_end += nglobals;
}

static inline uint64_t *get_global(uint64_t i) {
  return (OPERAND_STACK_SIZE_BEGIN - i - 1); // file->global_ptr + i;
}

static inline uint64_t pop_operand() {
  [[unlikely]] if (operand_stack_end == OPERAND_STACK_SIZE_BEGIN) {
    throw std::logic_error("op stack underflow");
  }
  --operand_stack_end;
  uint64_t result = *operand_stack_end;
  *operand_stack_end = 0;
  return result;
}

static inline void push_operand(uint64_t operand) {
  *operand_stack_end = operand;
  ++operand_stack_end; 
  [[unlikely]] if (operand_stack_end >= OPERAND_STACK_SIZE_END) {
    throw std::logic_error("op stack overflow");
  }
}

static inline void call_begin(uint64_t nargs, const char *next) {
  [[unlikely]] if (sp + nargs + 4 >= CALL_STACK_SIZE_END) {
    throw std::logic_error("call stack overflow");
  }
  for (int i = 0; i < nargs; ++i) {
    sp[i] = pop_operand();
  }
  sp[nargs] = reinterpret_cast<uint64_t>(next);
  sp[nargs + 1] = reinterpret_cast<uint64_t>(sp);
  sp[nargs + 2] = reinterpret_cast<uint64_t>(fp);
  sp[nargs + 3] = *closure_address;
  *closure_address = 0;
  fp = &sp[nargs];
  sp += (nargs + 4);
}

static inline void alloc_locals(uint64_t nlocals) {
  sp += nlocals;
  [[unlikely]] if (sp >= CALL_STACK_SIZE_END) {
    throw std::logic_error("call stack overflow");
  }
}

static inline uint64_t *get_local(uint64_t i) {
  return (sp - i - 1);
}

static void print_stacks() {
  fprintf(stderr, "\n\nstack:");
  for (uint64_t *i = operand_stack_end - 1; i >= OPERAND_STACK_SIZE_BEGIN; --i) {
    fprintf(stderr, " %li ", *i);
  }

  fprintf(stderr, "\n\ngloba + clos:");
  for (uint64_t *i = OPERAND_STACK_SIZE_BEGIN - 1; i >= memory_to_simulation + ALIGNMENT_FEATURE; --i) {
    fprintf(stderr, " %li ", *i);
  }

  fprintf(stderr, "\n\ncall stack:");
  for (uint64_t *i = sp - 1; i >= CALL_STACK_SIZE_BEGIN; --i) {
    fprintf(stderr, " %li (%lx) ", *i, *i);
  }
  fprintf(stderr, "\n\n");
}

static inline uint64_t *get_arg(uint64_t i) {
  return (fp - i - 1);
}

static inline uint64_t *get_closure(uint64_t i) {
  if (i >= LEN(TO_DATA((*closure_address))) - 1) {
    [[unlikely]] throw std::logic_error("bad access to closure");
  }
  return reinterpret_cast<uint64_t *>(*closure_address) + (i + 1); //  Value.Access i -> I (word_size * (i + 1), r15)
}

static inline const char *call_end() {
  const char *result = reinterpret_cast<char *>(fp[0]);
  uint64_t *need_sp = reinterpret_cast<uint64_t *>(fp[1]);
  *closure_address = fp[3];
  fp = reinterpret_cast<uint64_t *>(fp[2]);
  while (sp > need_sp && need_sp != 0) {
    --sp;
    *sp = 0;
  }
  sp = need_sp;
  return result;
}

static inline uint64_t make_boxed(uint64_t n) {
  return (n << 1) + 1;
}

static inline uint64_t make_unboxed(int64_t n) {
  return n >> 1;
}

static inline void check_unboxed(uint64_t n, const std::string &message) {
  [[unlikely]] if (!(n & 1)) {
    throw std::logic_error(message);
  }
}

#define CHECK_ARGS_NUMBER(addr, arg_number) \
        do { if (addr_to_args_number.find(addr) != addr_to_args_number.end()) { \
          [[unlikely]] if (addr_to_args_number[addr] != (arg_number)) { \
            throw std::logic_error("incorrect args number"); \
          } \
        } else { \
          addr_to_args_number[addr] = (arg_number); \
        } } while(0)

#define CHECK_LOCALS(i) do { [[unlikely]] if ((i) >= locals) throw std::logic_error("invalid local dereference"); } while(0)
#define CHECK_ARGS(i) do { [[unlikely]] if ((i) >= args) throw std::logic_error("invalid arg dereference"); } while(0)
#define CHECK_GLOBAL(i) do { [[unlikely]] if ((i) >= globals) throw std::logic_error("invalid global dereference"); } while(0)
#define CHECK_JMP_ADDR(addr) do { if (addr <= current_addr) { [[unlikely]] if (addr <= addr_of_function_begin) throw std::logic_error("invalid jump"); } else { addrs_jump_in_function.insert(addr); } } while (0)
#define CHECK_NUMBER_IS_ADEQUATE(n) do { [[unlikely]] if (n > 256) throw std::logic_error("inadequate constant"); } while (0)

static inline const char *safe_get_ip(const char* ip, size_t size) {
  [[unlikely]] if (ip + size - 1 > (char *)file + bytefile_size) {
    throw std::logic_error("file is not finishing");
  }
  return ip;
}

#undef INT
#undef BYTE
#define INT (ip += sizeof(int), *(int *)safe_get_ip(ip - sizeof(int), sizeof(int)))
#define BYTE (ip += 1, *safe_get_ip(ip - 1, 1))

static void check_file(FILE *f = stderr)
{
  const char *ip = file->code_ptr;
  
  bool was_begin = false;
  uint64_t globals = file->global_area_size;
  uint64_t locals = 0;
  uint64_t args = 0;
  std::unordered_map<uint64_t, uint64_t> addr_to_args_number;
  std::unordered_set<uint64_t> addrs_jump_in_function;
  std::unordered_set<uint64_t> function_begin_addrs;
  std::unordered_set<uint64_t> forward_calls;
  std::unordered_set<uint64_t> closure_begin_addrs;
  std::unordered_set<uint64_t> forward_ccalls;
  uint64_t addr_of_function_begin = 0;

  do
  {
    // print_code(ip);
    char x = BYTE,
         h = (x & 0xF0) >> 4,
         l = x & 0x0F;

    uint64_t current_addr = ip - file->code_ptr - 1;
    [[unlikely]] if (!was_begin && (h != 5 || l != 2 && l != 3) && h != 15) {
      throw std::logic_error("should be BEGIN instruction");
    }
    bool is_main_begin = current_addr == main_ptr;
    [[unlikely]] if (is_main_begin && (h != 5 || l != 2)) {
      throw std::logic_error("main should point to BEGIN");
    }
    if (forward_calls.find(current_addr) != forward_calls.end()) {
      [[unlikely]] if (h != 5 || l != 2) {
        throw std::logic_error("CALL must refer to BEGIN");
      } else {
        forward_calls.erase(forward_calls.find(current_addr));
      }
    }
    if (forward_ccalls.find(current_addr) != forward_ccalls.end()) {
      [[unlikely]] if (h != 5 || l != 3 && l != 2) {
        throw std::logic_error("CLOSURE must refer to BEGIN");
      } else {
        forward_ccalls.erase(forward_ccalls.find(current_addr));
      }
    }

    switch (h)
    {
    case 15:
      [[unlikely]] if (was_begin) {
        throw std::logic_error("invalid file: <end> before END");
      }
      [[unlikely]] if (main_ptr + file->code_ptr >= ip) {
        throw std::logic_error("main points outside the code");
      }
      [[unlikely]] if (!forward_calls.empty()) {
        throw std::logic_error("unresolved calls was found");
      }
      [[unlikely]] if (!forward_ccalls.empty()) {
        throw std::logic_error("unresolved closures was found");
        // for (auto ccal : forward_ccalls) {
        //   fprintf(stderr, "%lx\n", ccal); //
        // }
      }
      goto stop;

    /* BINOP */
    case 0: {
      [[unlikely]] if (l < 1 || l > 13) {
        throw std::logic_error("unknown BINOP");
      }
      break;
    }

    case 1:
      switch (l)
      {
      case 0: { // CONST
        uint64_t n = INT;
        break;
      }

      case 1: { // STRING
        const char *tag = STRING;
        break;
      }

      case 2: { // SEXP
        const char *tag = STRING;
        uint64_t n = INT;
        CHECK_NUMBER_IS_ADEQUATE(n);
        break;
      }

      [[unlikely]] case 3:
        throw std::logic_error("STI is temporary prohibited");

      case 4: // STA
        break;

      case 5: { // JMP
        uint64_t addr = INT;
        CHECK_JMP_ADDR(addr);
        break;
      }

      case 6: // END
        was_begin = false;
        for (auto addr : addrs_jump_in_function) {
          [[unlikely]] if (addr > current_addr) {
            throw std::logic_error("invalid jump");
          }
        }
        addrs_jump_in_function.clear();
        break;

      case 7: // RET
        break;

      case 8: // DROP
        break;

      case 9: // DUP
        break;

      case 10: // SWAP
        break;

      case 11: // ELEM
        break;

      default:
        FAIL;
      }
      break;
    [[unlikely]] case 3: // LDA
      throw std::logic_error("LDA is temporary prohibited");
    case 2: // LD
    case 4: { // ST
      uint64_t i = INT;
      switch (l)
      {
      case 0:
        CHECK_GLOBAL(i);
        break;
      case 1:
        CHECK_LOCALS(i);
        break;
      case 2:
        CHECK_ARGS(i);
        break;
      case 3:
        break;
      default:
        FAIL;
      }
      break;
    }

    case 5:
      switch (l)
      { // CJMPz
      case 0: {
        uint64_t addr = INT;
        CHECK_JMP_ADDR(addr);
        break;
      }

      case 1: { // CJMPnz
        uint64_t addr = INT;
        CHECK_JMP_ADDR(addr);
        break;
      }

      case 2: { // BEGIN
        uint64_t nargs = INT;
        uint64_t nlocals = INT;
        was_begin = true;
        CHECK_ARGS_NUMBER(current_addr, nargs);
        [[unlikely]] if (is_main_begin && nargs != 2) {
          throw std::logic_error("should be 2 args in main");
        }
        addr_of_function_begin = current_addr;
        function_begin_addrs.insert(addr_of_function_begin);
        args = nargs;
        locals = nlocals;
        break;
      }

      case 3: { // CBEGIN
        uint64_t nargs = INT;
        uint64_t nlocals = INT;
        was_begin = true;
        CHECK_ARGS_NUMBER((ip - file->code_ptr - 1), nargs);
        addr_of_function_begin = current_addr;
        closure_begin_addrs.insert(addr_of_function_begin);
        args = nargs;
        locals = nlocals;
        break;
      }

      case 4: { // CLOSURE
        uint64_t addr = INT;
        {
          int n = INT;
          CHECK_NUMBER_IS_ADEQUATE(n);
          for (int i = 0; i < n; i++)
          {
            uint64_t byte = BYTE;
            uint64_t number = INT;
            switch (byte)
            {
            case 0:
              CHECK_GLOBAL(number);
              break;
            case 1:
              CHECK_LOCALS(number);
              break;
            case 2:
              CHECK_ARGS(number);
              break;
            case 3:
              break;
            default:
              FAIL;
            }
          }
        };
        if (addr <= current_addr) {
          [[unlikely]] if (closure_begin_addrs.find(current_addr) == closure_begin_addrs.end()) {
            throw std::logic_error("CLOSURE must correspond BEGIN");
          }
        } else {
          forward_ccalls.insert(addr);
        }
        break;
      }

      case 5: { // CALLC
        uint64_t n = INT;
        break;
      }

      case 6: { // CALL
        uint64_t addr = INT;
        uint64_t arg_number = INT;
        CHECK_ARGS_NUMBER(addr, arg_number);
        if (addr <= current_addr) {
          [[unlikely]] if (function_begin_addrs.find(addr) == function_begin_addrs.end()) {
            throw std::logic_error("CALL must refer to BEGIN");
          }
        } else {
          forward_calls.insert(addr);
        }
        break;
      }

      case 7: { // TAG
        const char *tag = STRING;
        uint64_t n = INT;
        CHECK_NUMBER_IS_ADEQUATE(n);
        break;
      }

      case 8: { // ARRAY
        uint64_t n = INT;
        CHECK_NUMBER_IS_ADEQUATE(n);
        break;
      }

      case 9: { // FAIL
        uint64_t line = INT;
        uint64_t column = INT;
        break;
      }

      case 10: { // LINE
        uint64_t n = INT;
        break;
      }

      default:
        FAIL;
      }
      break;

    case 6: // PATT
      [[unlikely]] if (l >= 7) {
        throw std::logic_error("unsupported pattern for PATT");
      }
      break;

    case 7:
    {
      switch (l)
      {
      case 0: // Lread
        break;

      case 1: // Lwrite
        break;

      case 2: // Llength
        break;

      case 3: // Lstring
        break;

      case 4: { // Barray
        uint64_t n = INT;
        CHECK_NUMBER_IS_ADEQUATE(n);
        break;
      }

      default:
        FAIL;
      }
    }
    break;

    default:
      FAIL;
    }
  } while (1);
stop:
  return;
}

#undef INT
#undef BYTE
#define INT (ip += sizeof(int), *(int *)(ip - sizeof(int)))
#define BYTE *ip++

static void run_interpreter()
{
  uint64_t arg_numbers_checker = 2;
  const char *ip = main_ptr + file->code_ptr;
  __gc_init();
  __gc_stack_bottom = reinterpret_cast<size_t>(memory_to_simulation + sizeof(memory_to_simulation) / sizeof(memory_to_simulation[0]) - sizeof(void *));
  __gc_stack_top = (reinterpret_cast<size_t>(memory_to_simulation) + ALIGNMENT_FEATURE - sizeof(void *)) & (~0xFull);
  move_globals(file->global_area_size);
  do
  {
    // print_code(ip, file);
    char x = BYTE,
         h = (x & 0xF0) >> 4,
         l = x & 0x0F;
    // dump_heap();
    // print_stacks();

    switch (h)
    {
    /* BINOP  must be valid*/
    case 0: {
      uint64_t result;
      uint64_t first = make_unboxed(pop_operand());
      uint64_t second = make_unboxed(pop_operand());
      switch (l) {
        case 1: result = second + first; break;
        case 2: result = second - first; break;
        case 3: result = int64_t(second) * int64_t(first); break;
        case 4:
          if (first == 0) {
            throw std::logic_error("divide by zero");
          }
          result = int64_t(second) / int64_t(first); break;
        case 5:
          if (first == 0) {
            throw std::logic_error("divide by zero");
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
      case 0: { // CONST
        uint64_t n = INT;
        push_operand(make_boxed(n));
        break;
      }

      case 1: { // STRING
        uint64_t ptr = reinterpret_cast<uint64_t>(STRING);
        uint64_t allocated_ptr = reinterpret_cast<uint64_t>(Bstring(reinterpret_cast<aint *>(&ptr)));
        push_operand(allocated_ptr);
        break;
      }

      case 2: { // SEXP
        uint64_t ptr = reinterpret_cast<uint64_t>(STRING);
        uint64_t n = INT;
        aint tmp_array[n + 1];
        tmp_array[n] = LtagHash(reinterpret_cast<char *>(ptr));
        for (int i = n - 1; i >= 0; --i) {
          tmp_array[i] = pop_operand();
        }
        uint64_t allocated_value = reinterpret_cast<uint64_t>(Bsexp(tmp_array, static_cast<aint>(make_boxed(n + 1))));
        push_operand(allocated_value);
        break;
      }

      case 4: { // STA
        uint64_t v = pop_operand();
        uint64_t i = pop_operand();
        uint64_t y = pop_operand();
        push_operand(reinterpret_cast<uint64_t>(Bsta(reinterpret_cast<void *>(y), static_cast<aint>(i), reinterpret_cast<void *>(v))));
        break;
      }

      case 5: { // JMP
        uint64_t addr = INT;
        ip = addr + file->code_ptr;
        break;
      }

      case 6: // END
        ip = call_end();
        break;

      case 7: // RET
        ip = call_end();
        break;

      case 8: // DROP
        pop_operand();
        break;

      case 9: { // DUP
        uint64_t value = pop_operand();
        push_operand(value);
        push_operand(value);
        break;
      }

      case 10: { // SWAP
        uint64_t first = pop_operand();
        uint64_t second = pop_operand();
        push_operand(first);
        push_operand(second);
        break;
      }

      case 11: { // ELEM
        uint64_t i = pop_operand();
        uint64_t p = pop_operand();
        push_operand(reinterpret_cast<uint64_t>(Belem(reinterpret_cast<void *>(p), static_cast<aint>(i))));
        break;
      }
      }
      break;

    case 2: {// LD
      uint64_t variable;
      uint64_t i = INT;
      switch (l)
      {
      case 0:
        variable = *get_global(i);
        break;
      case 1:
        variable = *get_local(i);
        break;
      case 2:
        variable = *get_arg(i);
        break;
      case 3:
        variable = *get_closure(i);
        break;
      }
      push_operand(variable);
      break;
    }
    case 4: {// ST
      uint64_t i = INT;
      uint64_t value = pop_operand();
      push_operand(value);
      switch (l)
      {
      case 0: {
        *get_global(i) = value;
        break;
      }
      case 1: {
        *get_local(i) = value;
        break;
      }
      case 2: {
        *get_arg(i) = value;
        break;
      }
      case 3: {
        *get_closure(i) = value;
        break;
      }
      }
      break;
    }

    case 5:
      switch (l)
      {
      case 0: { // CJMPz
        uint64_t addr = INT;
        uint64_t value = make_unboxed(pop_operand());
        if (value == 0) {
          ip = addr + file->code_ptr;
        }
        break;
      }

      case 1: { // CJMPnz
        uint64_t addr = INT;
        uint64_t value = make_unboxed(pop_operand());
        if (value != 0) {
          ip = addr + file->code_ptr;
        }
        break;
      }

      case 2: { // BEGIN
        uint64_t nargs = INT;
        uint64_t nlocals = INT;
        [[unlikely]] if (nargs != arg_numbers_checker) {
          throw std::logic_error("incorrect argument number");
        }
        alloc_locals(nlocals);
        break;
      }

      case 3: { // CBEGIN
        uint64_t nargs = INT;
        uint64_t nlocals = INT;
        [[unlikely]] if (nargs != arg_numbers_checker) {
          throw std::logic_error("incorrect argument number");
        }
        alloc_locals(nlocals);
        break;
      }

      case 4: { // CLOSURE
        uint64_t addr = INT;
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
              args[i + 1] = *get_global(j);
              break;
            }
            case 1: {
              uint64_t j = INT;
              args[i + 1] = *get_local(j);
              break;
            }
            case 2: {
              uint64_t j = INT;
              args[i + 1] = *get_arg(j);
              break;
            }
            case 3: {
              uint64_t j = INT;
              args[i + 1] = *get_closure(j);
              break;
            }
            }
          }
        };
        push_operand(reinterpret_cast<uint64_t>(Bclosure(args, make_boxed(n))));
        break;
      }

      case 5: { // CALLC
        uint64_t args_number = INT;
        call_begin(args_number, ip);
        *closure_address = pop_operand();
        [[unlikely]] if (!Bclosure_tag_patt(reinterpret_cast<void *>(*closure_address))) {
          throw std::logic_error("closure expected");
        }
        arg_numbers_checker = args_number;
        ip = *reinterpret_cast<uint64_t *>(*closure_address) + file->code_ptr;
        break;
      }

      case 6: { // CALL
        uint64_t addr = INT;
        uint64_t args_number = INT;
        call_begin(args_number, ip);
        arg_numbers_checker = args_number;
        ip = addr + file->code_ptr;
        break;
      }

      case 7: { // TAG
        uint64_t string_ptr = reinterpret_cast<uint64_t>(STRING);
        uint64_t size = INT;
        uint64_t data = pop_operand();
        uint64_t value = Btag(
          reinterpret_cast<char *>(data), LtagHash(reinterpret_cast<char *>(string_ptr)), make_boxed(size));
        push_operand(value);
        break;
      }

      case 8: { // ARRAY
        uint64_t size = INT;
        uint64_t data = pop_operand();
        uint64_t value = Barray_patt(reinterpret_cast<void *>(data), make_boxed(size));
        push_operand(value);
        break;
      }

      case 9: { // FAIL
        uint64_t line = INT;
        uint64_t column = INT;
        uint64_t data = pop_operand();
        push_operand(data);
        Bmatch_failure(reinterpret_cast<void *>(data), const_cast<char *>(file_name), line, column);
        break;
      }

      case 10: { // LINE
        uint64_t n = INT;
        break;
      }
      }
      break;

    case 6: { // PATT
      switch (l) {
        case 0: { // strcmp
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
    {
      switch (l) // Lread
      {
      case 0:
        fprintf(stdout, " ");
        push_operand(Lread());
        break;

      case 1: {// Lwrite
        uint64_t value = pop_operand();
        check_unboxed(value, "Lwrite accept only numbers");
        Lwrite(value);
        push_operand(0);
        break;
      }

      case 2: // Llength
        push_operand(Llength(reinterpret_cast<void *>(pop_operand())));
        break;

      case 3: { // Lstring
        uint64_t value = pop_operand();
        push_operand(reinterpret_cast<uint64_t>(Lstring(reinterpret_cast<aint *>(&value))));
        break;
      }

      case 4: { // Barray
        uint64_t n = INT;
        aint args[n];
        for (int i = n - 1; i >= 0; --i) {
          args[i] = pop_operand();
        }
        push_operand(reinterpret_cast<uint64_t>(Barray(args, make_boxed(n))));
        break;
      }
      }
    }
    break;
    }
  } while (sp != nullptr);
  __shutdown();
}

static void find_main()
{
  bool found = false;
  for (int i = 0; i < file->public_symbols_number; i++) {
    const char *name =  get_public_name(file, i);
    uint64_t offset = get_public_offset(file, i);
    if (std::strcmp(name, "main") == 0) {
      main_ptr = (offset);
      found = true;
      break;
    }
  }
  [[unlikely]] if (!found) {
    throw std::logic_error("file doesn't contain main function");
  }
}

int main(int argc, char *argv[])
{
  [[unlikely]] if (argc != 2) {
    fprintf(stderr, "Error: should be 1 argument *.bc file!\n");
    std::exit(1);
  }
  file_name = argv[1];
  try {
    const bytefile *f = read_file(file_name);
    file = f;
    find_main();
    check_file();
  } catch (std::logic_error &e) {
    fprintf(stderr, "Error in bytecode: %s!\n", e.what());
    std::exit(1);
  }
  try {
    run_interpreter();
  } catch (std::logic_error &e) {
    fprintf(stderr, "Error: %s!\n", e.what());
    std::exit(1);
  }
  return 0;
}
