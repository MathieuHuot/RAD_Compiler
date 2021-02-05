#define CAML_NAME_SPACE
#include "caml/alloc.h"
#include "caml/mlvalues.h"

#include <math.h>

CAMLexport double caml_acosh(double x){
    return acosh(x);
}

CAMLexport double caml_asinh(double x){
    return asinh(x);
}

CAMLexport double caml_atanh(double x){
    return atanh(x);
}

CAMLprim value caml_acosh_float(value f) {
  return caml_copy_double(caml_acosh(Double_val(f)));
}

CAMLprim value caml_asinh_float(value f) {
  return caml_copy_double(caml_asinh(Double_val(f)));
}

CAMLprim value caml_atanh_float(value f) {
  return caml_copy_double(caml_atanh(Double_val(f)));
}
