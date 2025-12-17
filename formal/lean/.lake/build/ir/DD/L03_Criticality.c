// Lean compiler output
// Module: DD.L03_Criticality
// Imports: public import Init public import Mathlib.Data.Rat.Defs public import Mathlib.Data.Real.Basic public import Mathlib.Tactic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* lp_dd_DD_L03_Z__to__Q(lean_object*);
LEAN_EXPORT lean_object* lp_dd_DD_L03_T5;
LEAN_EXPORT lean_object* lp_dd_DD_L03_N__to__Z(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib_Rat_cast___at___00Rat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_dd_DD_L03_Q__to__R(lean_object*);
static lean_object* lp_dd_DD_L03_T5___closed__0;
lean_object* l_Rat_ofInt(lean_object*);
static lean_object* _init_lp_dd_DD_L03_T5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1000000u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_dd_DD_L03_T5() {
_start:
{
lean_object* x_1; 
x_1 = lp_dd_DD_L03_T5___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_dd_DD_L03_N__to__Z(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_dd_DD_L03_Z__to__Q(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Rat_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_dd_DD_L03_Q__to__R(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_mathlib_Rat_cast___at___00Rat_cast___at___00MeasureTheory_SimpleFunc_ennrealRatEmbed_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Rat_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Real_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_dd_DD_L03__Criticality(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Rat_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Real_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_dd_DD_L03_T5___closed__0 = _init_lp_dd_DD_L03_T5___closed__0();
lean_mark_persistent(lp_dd_DD_L03_T5___closed__0);
lp_dd_DD_L03_T5 = _init_lp_dd_DD_L03_T5();
lean_mark_persistent(lp_dd_DD_L03_T5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
