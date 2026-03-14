/* High-resolution monotonic timer for benchmarking.
   Returns nanoseconds as an unboxed OCaml int. */

#include <time.h>
#include <caml/mlvalues.h>

CAMLprim value caml_bench_monotonic_ns(value unit) {
  (void)unit;
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return Val_long(ts.tv_sec * 1000000000L + ts.tv_nsec);
}
