/* C stubs for fast Uint63 operations.
   All operate on OCaml tagged ints: runtime value = (uint63_val << 1) | 1.
   Long_val strips the tag, Val_long re-applies it. */

#include <caml/mlvalues.h>

/* Logical shift left.  Out-of-range shift returns 0. */
CAMLprim value caml_uint63_l_sl(value vx, value vy)
{
  long x = Long_val(vx);
  long y = Long_val(vy);
  if (y < 0 || y >= 63) return Val_long(0);
  return Val_long(x << y);
}

/* Logical shift right.  Out-of-range shift returns 0. */
CAMLprim value caml_uint63_l_sr(value vx, value vy)
{
  long x = Long_val(vx);
  long y = Long_val(vy);
  if (y < 0 || y >= 63) return Val_long(0);
  return Val_long((unsigned long)x >> y);
}

/* Unsigned division.  Division by zero returns 0. */
CAMLprim value caml_uint63_div(value vx, value vy)
{
  unsigned long x = (unsigned long)Long_val(vx);
  unsigned long y = (unsigned long)Long_val(vy);
  if (y == 0) return Val_long(0);
  return Val_long(x / y);
}

/* Unsigned remainder.  Remainder by zero returns x. */
CAMLprim value caml_uint63_rem(value vx, value vy)
{
  unsigned long x = (unsigned long)Long_val(vx);
  unsigned long y = (unsigned long)Long_val(vy);
  if (y == 0) return Val_long(x);
  return Val_long(x % y);
}

/* Count leading zeros of a 63-bit unsigned int. */
CAMLprim value caml_uint63_head0(value v)
{
  unsigned long x = (unsigned long)Long_val(v);
  if (x == 0) return Val_long(63);
  return Val_long(__builtin_clzl(x) - 1);
}

/* Count trailing zeros of a 63-bit unsigned int. */
CAMLprim value caml_uint63_tail0(value v)
{
  unsigned long x = (unsigned long)Long_val(v);
  if (x == 0) return Val_long(63);
  return Val_long(__builtin_ctzl(x));
}
