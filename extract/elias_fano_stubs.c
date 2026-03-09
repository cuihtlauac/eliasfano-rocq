/* C stubs for Elias-Fano: popcount and ctz.
   These are the only unverified code in the trust chain.
   Review surface: 6 lines of logic. */

#include <caml/mlvalues.h>

CAMLprim value caml_ef_popcount(value v) {
  return Val_long(__builtin_popcountl(Long_val(v)));
}

CAMLprim value caml_ef_ctz(value v) {
  long x = Long_val(v);
  return Val_long(x == 0 ? 63 : __builtin_ctzl(x));
}
