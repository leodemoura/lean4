// Lean compiler output
// Module: init.lean.ir.type_check
// Imports: init.lean.ir.instances init.lean.ir.format init.control.combinators
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_lean_ir_check__arg__types___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg___boxed(obj*, obj*);
obj* l_lean_ir_set__result__types___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_phi_check___boxed(obj*, obj*, obj*);
uint8 l_lean_ir_is__bitwise__ty(uint8);
obj* l_lean_ir_check__result__type___main___boxed(obj*, obj*, obj*, obj*);
uint8 l_lean_ir_is__nonfloat__arith__ty(uint8);
uint8 l_lean_ir_is__signed__arith__ty(uint8);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
obj* l_lean_ir_valid__assign__unop__types___closed__4;
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_terminator_check(obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2___boxed(obj*, obj*);
obj* l_lean_ir_set__result__types(obj*, obj*, obj*, obj*);
obj* l_lean_ir_terminator_to__format___main(obj*);
obj* l_lean_ir_match__type(obj*, uint8, uint8, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1___boxed(obj*, obj*);
obj* l_lean_ir_instr_to__format___main(obj*);
obj* l_lean_ir_match__type___closed__5;
obj* l_lean_ir_check__ne__type(obj*, uint8, obj*, obj*);
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_check__ne__type___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_set__type___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_phi_infer__types(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check___main___spec__1(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_set__type___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_get__type___spec__1(obj*, obj*);
obj* l_lean_ir_check__arg__types___main(obj*, obj*, obj*, obj*);
uint8 l_lean_ir_valid__assign__unop__types(uint8, uint8, uint8);
obj* l_lean_ir_type__check___closed__1;
obj* l_lean_ir_decl_infer__types(obj*, obj*, obj*);
obj* l_lean_ir_is__nonfloat__arith__ty___closed__2;
obj* l_lean_ir_block_check(obj*, obj*, obj*);
obj* l_lean_ir_type__check___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_set__type___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_ir_phi_infer__types___boxed(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(obj*);
obj* l_lean_ir_set__result__types___main___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_type_to__format___main(uint8);
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_decl_check___main(obj*, obj*, obj*);
obj* l_lean_ir_type2id___main(uint8);
obj* l_lean_ir_block_infer__types(obj*, obj*, obj*);
obj* l_lean_ir_instr_check___closed__1;
obj* l_lean_ir_instr_check___closed__3;
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_get__decl___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_ir_instr_infer__types(obj*, obj*, obj*);
obj* l_lean_ir_get__decl___closed__1;
obj* l_lean_ir_decl_check(obj*, obj*, obj*);
obj* l_lean_ir_check__ne__type___closed__1;
obj* l_rbmap_find___main___at_lean_ir_get__type___spec__1___boxed(obj*, obj*);
obj* l_lean_ir_valid__assign__unop__types___closed__3;
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_ir_instr_check___closed__5;
obj* l_lean_ir_invalid__literal___rarg(obj*);
uint8 l_lean_ir_is__arith__ty(uint8);
obj* l_lean_ir_check__type___closed__2;
obj* l_lean_ir_type__check___lambda__2___boxed(obj*, obj*, obj*);
obj* l_lean_ir_invalid__literal___rarg___closed__1;
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(obj*);
obj* l_lean_ir_type__check___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_ir_arg_infer__types___boxed(obj*, obj*, obj*);
obj* l_lean_ir_invalid__literal___rarg___boxed(obj*);
obj* l_rbmap_insert___main___at_lean_ir_set__type___spec__1(obj*, obj*, uint8);
extern obj* l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_decl_header___main(obj*);
obj* l_lean_ir_type__checker__m_run___rarg___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_is__bitshift__ty___boxed(obj*);
obj* l_lean_ir_instr_check(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1(obj*, obj*);
obj* l_lean_ir_phi_to__format___main(obj*);
obj* l_lean_ir_get__type(obj*, obj*, obj*);
obj* l_lean_ir_check__ne__type___closed__2;
obj* l_lean_ir_type__checker__m;
obj* l_lean_ir_match__type___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_match__type___closed__2;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_lean_ir_is__bitshift__ty(uint8);
obj* l_lean_ir_type__checker__m_run___rarg(obj*, obj*, obj*);
obj* l_lean_ir_infer__types(obj*, obj*);
extern obj* l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
obj* l_rbnode_insert___at_lean_ir_set__type___spec__2(obj*, obj*, uint8);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_instr_check___closed__4;
obj* l_lean_ir_valid__assign__unop__types___closed__2;
obj* l_lean_ir_decl_infer__types___main(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_match__type___closed__4;
obj* l_lean_ir_type__checker__m_run(obj*);
obj* l_lean_ir_get__decl(obj*, obj*, obj*);
uint8 l_lean_ir_valid__assign__binop__types(uint8, uint8, uint8, uint8);
obj* l_lean_ir_match__type___closed__3;
obj* l_lean_ir_check__arg__types(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
extern obj* l_int_zero;
obj* l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_lean_ir_invalid__literal(obj*);
obj* l_lean_ir_set__result__types___main(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(obj*, obj*);
obj* l_lean_ir_valid__assign__binop__types___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_check__type(obj*, uint8, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_set__type___spec__3(obj*, obj*, uint8);
obj* l_lean_ir_instr_check___closed__2;
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2___boxed(obj*);
obj* l_lean_ir_check__result__type___main(obj*, obj*, obj*, obj*);
obj* l_lean_ir_get__type___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_ir_infer__types___boxed(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_terminator_check___closed__1;
obj* l_lean_ir_check__result__type___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_is__arith__ty___boxed(obj*);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_phi_check(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(obj*);
obj* l_lean_ir_is__nonfloat__arith__ty___boxed(obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_set__type___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2(obj*);
obj* l_lean_ir_get__type___boxed(obj*, obj*, obj*);
obj* l_lean_ir_check__arg__types___main___closed__1;
obj* l_lean_ir_check__result__type(obj*, obj*, obj*, obj*);
extern obj* l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_set__type(obj*, uint8, obj*, obj*);
obj* l_lean_ir_valid__assign__unop__types___closed__1;
obj* l_lean_ir_valid__assign__unop__types___boxed(obj*, obj*, obj*);
obj* l_lean_ir_literal_check___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_is__signed__arith__ty___boxed(obj*);
obj* l_lean_ir_check__arg__types___main___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_type__check(obj*, obj*);
obj* l_lean_ir_check__type___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(obj*, obj*, obj*);
extern obj* l_lean_ir_mk__context;
obj* l_lean_ir_literal_check(obj*, uint8, obj*, obj*);
obj* l_lean_ir_type__check___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1;
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_lean_ir_type__check___lambda__2(obj*, obj*, obj*);
obj* l_lean_ir_match__type___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_check__type___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_is__bitwise__ty___boxed(obj*);
obj* l_lean_ir_is__nonfloat__arith__ty___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__2(obj*, obj*, obj*);
namespace lean {
uint8 int_dec_lt(obj*, obj*);
}
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2(obj*, obj*);
obj* l_lean_ir_terminator_check___boxed(obj*, obj*, obj*);
obj* l_lean_ir_invalid__literal___boxed(obj*);
obj* l_lean_ir_is__arith__ty___closed__1;
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_lean_ir_arg_infer__types(obj*, obj*, obj*);
obj* l_lean_ir_type__checker__m_run___boxed(obj*);
extern obj* l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
uint8 l_lean_ir_is__signed__arith__ty(uint8 x_0) {
_start:
{
switch (x_0) {
case 6:
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
case 7:
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
case 8:
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
case 9:
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
case 10:
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
default:
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
}
obj* l_lean_ir_is__signed__arith__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__signed__arith__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_lean_ir_is__arith__ty___closed__1() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 0;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
uint8 l_lean_ir_is__arith__ty(uint8 x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_lean_ir_type2id___main(x_0);
x_2 = l_lean_ir_is__arith__ty___closed__1;
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
obj* l_lean_ir_is__arith__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__arith__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_lean_ir_is__nonfloat__arith__ty___closed__1() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 10;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_is__nonfloat__arith__ty___closed__2() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 9;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
uint8 l_lean_ir_is__nonfloat__arith__ty(uint8 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_is__arith__ty(x_0);
if (x_1 == 0)
{
if (x_1 == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = l_lean_ir_type2id___main(x_0);
x_3 = l_lean_ir_is__nonfloat__arith__ty___closed__1;
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_2);
if (x_4 == 0)
{
return x_1;
}
else
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = l_lean_ir_type2id___main(x_0);
x_8 = l_lean_ir_is__nonfloat__arith__ty___closed__2;
x_9 = lean::nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
if (x_1 == 0)
{
lean::dec(x_7);
return x_1;
}
else
{
obj* x_11; uint8 x_12; 
x_11 = l_lean_ir_is__nonfloat__arith__ty___closed__1;
x_12 = lean::nat_dec_eq(x_7, x_11);
lean::dec(x_7);
if (x_12 == 0)
{
return x_1;
}
else
{
uint8 x_14; 
x_14 = 0;
return x_14;
}
}
}
else
{
uint8 x_16; 
lean::dec(x_7);
x_16 = 0;
return x_16;
}
}
}
}
obj* l_lean_ir_is__nonfloat__arith__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__nonfloat__arith__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_ir_is__bitwise__ty(uint8 x_0) {
_start:
{
switch (x_0) {
case 6:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 7:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 8:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
case 9:
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
case 10:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
default:
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
}
obj* l_lean_ir_is__bitwise__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__bitwise__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_ir_is__bitshift__ty(uint8 x_0) {
_start:
{
switch (x_0) {
case 0:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 9:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 10:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
case 11:
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
default:
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
}
obj* l_lean_ir_is__bitshift__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__bitshift__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_lean_ir_valid__assign__unop__types___closed__1() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 11;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_valid__assign__unop__types___closed__2() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 5;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_valid__assign__unop__types___closed__3() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 3;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_valid__assign__unop__types___closed__4() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 7;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
uint8 l_lean_ir_valid__assign__unop__types(uint8 x_0, uint8 x_1, uint8 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; 
switch (x_0) {
case 0:
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = l_lean_ir_type2id___main(x_2);
x_14 = l_lean_ir_type2id___main(x_1);
x_15 = lean::nat_dec_eq(x_13, x_14);
lean::dec(x_14);
lean::dec(x_13);
if (x_15 == 0)
{
uint8 x_18; 
x_18 = 0;
return x_18;
}
else
{
uint8 x_19; 
x_19 = l_lean_ir_is__bitwise__ty(x_2);
return x_19;
}
}
case 1:
{
obj* x_20; obj* x_21; uint8 x_22; 
x_20 = l_lean_ir_type2id___main(x_2);
x_21 = l_lean_ir_type2id___main(x_1);
x_22 = lean::nat_dec_eq(x_20, x_21);
lean::dec(x_21);
lean::dec(x_20);
if (x_22 == 0)
{
uint8 x_25; 
x_25 = 0;
return x_25;
}
else
{
uint8 x_26; 
x_26 = l_lean_ir_is__signed__arith__ty(x_2);
return x_26;
}
}
case 2:
{
obj* x_27; 
x_27 = lean::box(0);
x_3 = x_27;
goto lbl_4;
}
case 3:
{
obj* x_28; 
x_28 = lean::box(0);
x_3 = x_28;
goto lbl_4;
}
case 7:
{
obj* x_29; obj* x_30; uint8 x_31; 
x_29 = l_lean_ir_type2id___main(x_1);
x_30 = l_lean_ir_valid__assign__unop__types___closed__1;
x_31 = lean::nat_dec_eq(x_29, x_30);
lean::dec(x_29);
if (x_31 == 0)
{
uint8 x_33; 
x_33 = 1;
return x_33;
}
else
{
uint8 x_34; 
x_34 = 0;
return x_34;
}
}
case 8:
{
obj* x_35; obj* x_36; uint8 x_37; 
x_35 = l_lean_ir_type2id___main(x_1);
x_36 = l_lean_ir_valid__assign__unop__types___closed__1;
x_37 = lean::nat_dec_eq(x_35, x_36);
lean::dec(x_35);
if (x_37 == 0)
{
uint8 x_39; 
x_39 = 0;
return x_39;
}
else
{
obj* x_40; obj* x_41; uint8 x_42; 
x_40 = l_lean_ir_type2id___main(x_2);
x_41 = l_lean_ir_valid__assign__unop__types___closed__3;
x_42 = lean::nat_dec_eq(x_40, x_41);
if (x_42 == 0)
{
obj* x_43; uint8 x_44; 
x_43 = l_lean_ir_valid__assign__unop__types___closed__4;
x_44 = lean::nat_dec_eq(x_40, x_43);
lean::dec(x_40);
if (x_44 == 0)
{
uint8 x_46; 
x_46 = 0;
return x_46;
}
else
{
uint8 x_47; 
x_47 = 1;
return x_47;
}
}
else
{
uint8 x_49; 
lean::dec(x_40);
x_49 = 1;
return x_49;
}
}
}
case 9:
{
obj* x_50; obj* x_51; uint8 x_52; 
x_50 = l_lean_ir_type2id___main(x_2);
x_51 = l_lean_ir_valid__assign__unop__types___closed__1;
x_52 = lean::nat_dec_eq(x_50, x_51);
lean::dec(x_50);
if (x_52 == 0)
{
uint8 x_54; 
x_54 = 0;
return x_54;
}
else
{
obj* x_55; obj* x_56; uint8 x_57; 
x_55 = l_lean_ir_type2id___main(x_1);
x_56 = l_lean_ir_valid__assign__unop__types___closed__3;
x_57 = lean::nat_dec_eq(x_55, x_56);
if (x_57 == 0)
{
obj* x_58; uint8 x_59; 
x_58 = l_lean_ir_valid__assign__unop__types___closed__4;
x_59 = lean::nat_dec_eq(x_55, x_58);
lean::dec(x_55);
if (x_59 == 0)
{
uint8 x_61; 
x_61 = 0;
return x_61;
}
else
{
uint8 x_62; 
x_62 = 1;
return x_62;
}
}
else
{
uint8 x_64; 
lean::dec(x_55);
x_64 = 1;
return x_64;
}
}
}
case 10:
{
obj* x_65; 
x_65 = lean::box(0);
x_7 = x_65;
goto lbl_8;
}
case 11:
{
obj* x_66; 
x_66 = lean::box(0);
x_7 = x_66;
goto lbl_8;
}
case 12:
{
obj* x_67; 
x_67 = lean::box(0);
x_9 = x_67;
goto lbl_10;
}
case 13:
{
obj* x_68; 
x_68 = lean::box(0);
x_9 = x_68;
goto lbl_10;
}
case 14:
{
obj* x_69; 
x_69 = lean::box(0);
x_9 = x_69;
goto lbl_10;
}
case 15:
{
obj* x_70; obj* x_71; uint8 x_72; 
x_70 = l_lean_ir_type2id___main(x_1);
x_71 = l_lean_ir_valid__assign__unop__types___closed__1;
x_72 = lean::nat_dec_eq(x_70, x_71);
lean::dec(x_70);
if (x_72 == 0)
{
uint8 x_74; 
x_74 = 0;
return x_74;
}
else
{
obj* x_75; uint8 x_76; 
x_75 = l_lean_ir_type2id___main(x_2);
x_76 = lean::nat_dec_eq(x_75, x_71);
lean::dec(x_75);
if (x_76 == 0)
{
uint8 x_78; 
x_78 = 0;
return x_78;
}
else
{
uint8 x_79; 
x_79 = 1;
return x_79;
}
}
}
case 16:
{
obj* x_80; 
x_80 = lean::box(0);
x_11 = x_80;
goto lbl_12;
}
case 17:
{
obj* x_81; 
x_81 = lean::box(0);
x_11 = x_81;
goto lbl_12;
}
default:
{
obj* x_82; 
x_82 = lean::box(0);
x_5 = x_82;
goto lbl_6;
}
}
lbl_4:
{
obj* x_84; obj* x_85; uint8 x_86; 
lean::dec(x_3);
x_84 = l_lean_ir_type2id___main(x_2);
x_85 = l_lean_ir_type2id___main(x_1);
x_86 = lean::nat_dec_eq(x_84, x_85);
lean::dec(x_85);
if (x_86 == 0)
{
uint8 x_89; 
lean::dec(x_84);
x_89 = 0;
return x_89;
}
else
{
obj* x_90; uint8 x_91; 
x_90 = l_lean_ir_valid__assign__unop__types___closed__1;
x_91 = lean::nat_dec_eq(x_84, x_90);
lean::dec(x_84);
if (x_91 == 0)
{
uint8 x_93; 
x_93 = 0;
return x_93;
}
else
{
uint8 x_94; 
x_94 = 1;
return x_94;
}
}
}
lbl_6:
{
obj* x_96; obj* x_97; uint8 x_98; 
lean::dec(x_5);
x_96 = l_lean_ir_type2id___main(x_2);
x_97 = l_lean_ir_valid__assign__unop__types___closed__1;
x_98 = lean::nat_dec_eq(x_96, x_97);
lean::dec(x_96);
if (x_98 == 0)
{
uint8 x_100; 
x_100 = 0;
return x_100;
}
else
{
obj* x_101; obj* x_102; uint8 x_103; 
x_101 = l_lean_ir_type2id___main(x_1);
x_102 = l_lean_ir_is__arith__ty___closed__1;
x_103 = lean::nat_dec_eq(x_101, x_102);
lean::dec(x_101);
if (x_103 == 0)
{
uint8 x_105; 
x_105 = 0;
return x_105;
}
else
{
uint8 x_106; 
x_106 = 1;
return x_106;
}
}
}
lbl_8:
{
obj* x_108; obj* x_109; uint8 x_110; 
lean::dec(x_7);
x_108 = l_lean_ir_type2id___main(x_2);
x_109 = l_lean_ir_valid__assign__unop__types___closed__1;
x_110 = lean::nat_dec_eq(x_108, x_109);
lean::dec(x_108);
if (x_110 == 0)
{
uint8 x_112; 
x_112 = 0;
return x_112;
}
else
{
obj* x_113; uint8 x_114; 
x_113 = l_lean_ir_type2id___main(x_1);
x_114 = lean::nat_dec_eq(x_113, x_109);
lean::dec(x_113);
if (x_114 == 0)
{
uint8 x_116; 
x_116 = 0;
return x_116;
}
else
{
uint8 x_117; 
x_117 = 1;
return x_117;
}
}
}
lbl_10:
{
obj* x_119; obj* x_120; uint8 x_121; 
lean::dec(x_9);
x_119 = l_lean_ir_type2id___main(x_1);
x_120 = l_lean_ir_valid__assign__unop__types___closed__2;
x_121 = lean::nat_dec_eq(x_119, x_120);
lean::dec(x_119);
if (x_121 == 0)
{
uint8 x_123; 
x_123 = 0;
return x_123;
}
else
{
obj* x_124; obj* x_125; uint8 x_126; 
x_124 = l_lean_ir_type2id___main(x_2);
x_125 = l_lean_ir_valid__assign__unop__types___closed__1;
x_126 = lean::nat_dec_eq(x_124, x_125);
lean::dec(x_124);
if (x_126 == 0)
{
uint8 x_128; 
x_128 = 0;
return x_128;
}
else
{
uint8 x_129; 
x_129 = 1;
return x_129;
}
}
}
lbl_12:
{
obj* x_131; obj* x_132; uint8 x_133; 
lean::dec(x_11);
x_131 = l_lean_ir_type2id___main(x_1);
x_132 = l_lean_ir_valid__assign__unop__types___closed__3;
x_133 = lean::nat_dec_eq(x_131, x_132);
lean::dec(x_131);
if (x_133 == 0)
{
uint8 x_135; 
x_135 = 0;
return x_135;
}
else
{
obj* x_136; obj* x_137; uint8 x_138; 
x_136 = l_lean_ir_type2id___main(x_2);
x_137 = l_lean_ir_valid__assign__unop__types___closed__1;
x_138 = lean::nat_dec_eq(x_136, x_137);
lean::dec(x_136);
if (x_138 == 0)
{
uint8 x_140; 
x_140 = 0;
return x_140;
}
else
{
uint8 x_141; 
x_141 = 1;
return x_141;
}
}
}
}
}
obj* l_lean_ir_valid__assign__unop__types___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; uint8 x_6; obj* x_7; 
x_3 = lean::unbox(x_0);
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = l_lean_ir_valid__assign__unop__types(x_3, x_4, x_5);
x_7 = lean::box(x_6);
return x_7;
}
}
uint8 l_lean_ir_valid__assign__binop__types(uint8 x_0, uint8 x_1, uint8 x_2, uint8 x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; 
switch (x_0) {
case 0:
{
obj* x_18; 
x_18 = lean::box(0);
x_4 = x_18;
goto lbl_5;
}
case 1:
{
obj* x_19; 
x_19 = lean::box(0);
x_4 = x_19;
goto lbl_5;
}
case 2:
{
obj* x_20; 
x_20 = lean::box(0);
x_4 = x_20;
goto lbl_5;
}
case 3:
{
obj* x_21; 
x_21 = lean::box(0);
x_4 = x_21;
goto lbl_5;
}
case 4:
{
obj* x_22; obj* x_23; uint8 x_24; 
x_22 = l_lean_ir_type2id___main(x_1);
x_23 = l_lean_ir_type2id___main(x_2);
x_24 = lean::nat_dec_eq(x_22, x_23);
lean::dec(x_23);
if (x_24 == 0)
{
uint8 x_27; 
lean::dec(x_22);
x_27 = 0;
return x_27;
}
else
{
obj* x_28; uint8 x_29; 
x_28 = l_lean_ir_type2id___main(x_3);
x_29 = lean::nat_dec_eq(x_22, x_28);
lean::dec(x_28);
lean::dec(x_22);
if (x_29 == 0)
{
uint8 x_32; 
x_32 = 0;
return x_32;
}
else
{
uint8 x_33; 
x_33 = l_lean_ir_is__nonfloat__arith__ty(x_1);
return x_33;
}
}
}
case 10:
{
obj* x_34; 
x_34 = lean::box(0);
x_8 = x_34;
goto lbl_9;
}
case 11:
{
obj* x_35; 
x_35 = lean::box(0);
x_8 = x_35;
goto lbl_9;
}
case 12:
{
obj* x_36; 
x_36 = lean::box(0);
x_10 = x_36;
goto lbl_11;
}
case 13:
{
obj* x_37; 
x_37 = lean::box(0);
x_10 = x_37;
goto lbl_11;
}
case 14:
{
obj* x_38; 
x_38 = lean::box(0);
x_10 = x_38;
goto lbl_11;
}
case 15:
{
obj* x_39; 
x_39 = lean::box(0);
x_12 = x_39;
goto lbl_13;
}
case 16:
{
obj* x_40; 
x_40 = lean::box(0);
x_12 = x_40;
goto lbl_13;
}
case 17:
{
obj* x_41; 
x_41 = lean::box(0);
x_14 = x_41;
goto lbl_15;
}
case 18:
{
obj* x_42; 
x_42 = lean::box(0);
x_14 = x_42;
goto lbl_15;
}
case 19:
{
obj* x_43; 
x_43 = lean::box(0);
x_16 = x_43;
goto lbl_17;
}
case 20:
{
obj* x_44; 
x_44 = lean::box(0);
x_16 = x_44;
goto lbl_17;
}
case 21:
{
obj* x_45; 
x_45 = lean::box(0);
x_16 = x_45;
goto lbl_17;
}
case 22:
{
obj* x_46; 
x_46 = lean::box(0);
x_16 = x_46;
goto lbl_17;
}
case 23:
{
obj* x_47; obj* x_48; uint8 x_49; 
x_47 = l_lean_ir_type2id___main(x_2);
x_48 = l_lean_ir_valid__assign__unop__types___closed__1;
x_49 = lean::nat_dec_eq(x_47, x_48);
lean::dec(x_47);
if (x_49 == 0)
{
uint8 x_51; 
x_51 = 0;
return x_51;
}
else
{
obj* x_52; obj* x_53; uint8 x_54; 
x_52 = l_lean_ir_type2id___main(x_3);
x_53 = l_lean_ir_valid__assign__unop__types___closed__2;
x_54 = lean::nat_dec_eq(x_52, x_53);
lean::dec(x_52);
if (x_54 == 0)
{
uint8 x_56; 
x_56 = 0;
return x_56;
}
else
{
uint8 x_57; 
x_57 = 1;
return x_57;
}
}
}
case 24:
{
obj* x_58; obj* x_59; uint8 x_60; 
x_58 = l_lean_ir_type2id___main(x_1);
x_59 = l_lean_ir_valid__assign__unop__types___closed__1;
x_60 = lean::nat_dec_eq(x_58, x_59);
lean::dec(x_58);
if (x_60 == 0)
{
uint8 x_62; 
x_62 = 0;
return x_62;
}
else
{
obj* x_63; uint8 x_64; 
x_63 = l_lean_ir_type2id___main(x_2);
x_64 = lean::nat_dec_eq(x_63, x_59);
lean::dec(x_63);
if (x_64 == 0)
{
uint8 x_66; 
x_66 = 0;
return x_66;
}
else
{
uint8 x_67; 
x_67 = 1;
return x_67;
}
}
}
case 25:
{
obj* x_68; obj* x_69; uint8 x_70; 
x_68 = l_lean_ir_type2id___main(x_1);
x_69 = l_lean_ir_valid__assign__unop__types___closed__1;
x_70 = lean::nat_dec_eq(x_68, x_69);
lean::dec(x_68);
if (x_70 == 0)
{
uint8 x_72; 
x_72 = 0;
return x_72;
}
else
{
obj* x_73; uint8 x_74; 
x_73 = l_lean_ir_type2id___main(x_2);
x_74 = lean::nat_dec_eq(x_73, x_69);
lean::dec(x_73);
if (x_74 == 0)
{
uint8 x_76; 
x_76 = 0;
return x_76;
}
else
{
obj* x_77; obj* x_78; uint8 x_79; 
x_77 = l_lean_ir_type2id___main(x_3);
x_78 = l_lean_ir_valid__assign__unop__types___closed__3;
x_79 = lean::nat_dec_eq(x_77, x_78);
lean::dec(x_77);
if (x_79 == 0)
{
uint8 x_81; 
x_81 = 0;
return x_81;
}
else
{
uint8 x_82; 
x_82 = 1;
return x_82;
}
}
}
}
case 26:
{
obj* x_83; obj* x_84; uint8 x_85; 
x_83 = l_lean_ir_type2id___main(x_1);
x_84 = l_lean_ir_valid__assign__unop__types___closed__1;
x_85 = lean::nat_dec_eq(x_83, x_84);
lean::dec(x_83);
if (x_85 == 0)
{
uint8 x_87; 
x_87 = 0;
return x_87;
}
else
{
obj* x_88; uint8 x_89; 
x_88 = l_lean_ir_type2id___main(x_2);
x_89 = lean::nat_dec_eq(x_88, x_84);
lean::dec(x_88);
if (x_89 == 0)
{
uint8 x_91; 
x_91 = 0;
return x_91;
}
else
{
obj* x_92; uint8 x_93; 
x_92 = l_lean_ir_type2id___main(x_3);
x_93 = lean::nat_dec_eq(x_92, x_84);
lean::dec(x_92);
if (x_93 == 0)
{
uint8 x_95; 
x_95 = 0;
return x_95;
}
else
{
uint8 x_96; 
x_96 = 1;
return x_96;
}
}
}
}
default:
{
obj* x_97; 
x_97 = lean::box(0);
x_6 = x_97;
goto lbl_7;
}
}
lbl_5:
{
obj* x_99; obj* x_100; uint8 x_101; 
lean::dec(x_4);
x_99 = l_lean_ir_type2id___main(x_1);
x_100 = l_lean_ir_type2id___main(x_2);
x_101 = lean::nat_dec_eq(x_99, x_100);
lean::dec(x_100);
if (x_101 == 0)
{
uint8 x_104; 
lean::dec(x_99);
x_104 = 0;
return x_104;
}
else
{
obj* x_105; uint8 x_106; 
x_105 = l_lean_ir_type2id___main(x_3);
x_106 = lean::nat_dec_eq(x_99, x_105);
lean::dec(x_105);
lean::dec(x_99);
if (x_106 == 0)
{
uint8 x_109; 
x_109 = 0;
return x_109;
}
else
{
uint8 x_110; 
x_110 = l_lean_ir_is__arith__ty(x_1);
return x_110;
}
}
}
lbl_7:
{
obj* x_112; obj* x_113; uint8 x_114; 
lean::dec(x_6);
x_112 = l_lean_ir_type2id___main(x_1);
x_113 = l_lean_ir_type2id___main(x_2);
x_114 = lean::nat_dec_eq(x_112, x_113);
lean::dec(x_113);
if (x_114 == 0)
{
uint8 x_117; 
lean::dec(x_112);
x_117 = 0;
return x_117;
}
else
{
obj* x_118; uint8 x_119; 
x_118 = l_lean_ir_type2id___main(x_3);
x_119 = lean::nat_dec_eq(x_112, x_118);
lean::dec(x_118);
if (x_119 == 0)
{
uint8 x_122; 
lean::dec(x_112);
x_122 = 0;
return x_122;
}
else
{
obj* x_123; uint8 x_124; 
x_123 = l_lean_ir_valid__assign__unop__types___closed__1;
x_124 = lean::nat_dec_eq(x_112, x_123);
lean::dec(x_112);
if (x_124 == 0)
{
uint8 x_126; 
x_126 = 0;
return x_126;
}
else
{
uint8 x_127; 
x_127 = 1;
return x_127;
}
}
}
}
lbl_9:
{
obj* x_129; obj* x_130; uint8 x_131; 
lean::dec(x_8);
x_129 = l_lean_ir_type2id___main(x_1);
x_130 = l_lean_ir_type2id___main(x_2);
x_131 = lean::nat_dec_eq(x_129, x_130);
lean::dec(x_130);
if (x_131 == 0)
{
uint8 x_134; 
lean::dec(x_129);
x_134 = 0;
return x_134;
}
else
{
obj* x_135; uint8 x_136; 
x_135 = l_lean_ir_type2id___main(x_3);
x_136 = lean::nat_dec_eq(x_129, x_135);
lean::dec(x_135);
lean::dec(x_129);
if (x_136 == 0)
{
uint8 x_139; 
x_139 = 0;
return x_139;
}
else
{
uint8 x_140; 
x_140 = l_lean_ir_is__bitshift__ty(x_1);
return x_140;
}
}
}
lbl_11:
{
obj* x_142; obj* x_143; uint8 x_144; 
lean::dec(x_10);
x_142 = l_lean_ir_type2id___main(x_1);
x_143 = l_lean_ir_type2id___main(x_2);
x_144 = lean::nat_dec_eq(x_142, x_143);
lean::dec(x_143);
if (x_144 == 0)
{
uint8 x_147; 
lean::dec(x_142);
x_147 = 0;
return x_147;
}
else
{
obj* x_148; uint8 x_149; 
x_148 = l_lean_ir_type2id___main(x_3);
x_149 = lean::nat_dec_eq(x_142, x_148);
lean::dec(x_148);
lean::dec(x_142);
if (x_149 == 0)
{
uint8 x_152; 
x_152 = 0;
return x_152;
}
else
{
uint8 x_153; 
x_153 = l_lean_ir_is__bitwise__ty(x_1);
return x_153;
}
}
}
lbl_13:
{
obj* x_155; obj* x_156; uint8 x_157; 
lean::dec(x_12);
x_155 = l_lean_ir_type2id___main(x_1);
x_156 = l_lean_ir_is__arith__ty___closed__1;
x_157 = lean::nat_dec_eq(x_155, x_156);
lean::dec(x_155);
if (x_157 == 0)
{
uint8 x_159; 
x_159 = 0;
return x_159;
}
else
{
obj* x_160; obj* x_161; uint8 x_162; 
x_160 = l_lean_ir_type2id___main(x_2);
x_161 = l_lean_ir_type2id___main(x_3);
x_162 = lean::nat_dec_eq(x_160, x_161);
lean::dec(x_161);
lean::dec(x_160);
if (x_162 == 0)
{
uint8 x_165; 
x_165 = 0;
return x_165;
}
else
{
uint8 x_166; 
x_166 = l_lean_ir_is__arith__ty(x_2);
return x_166;
}
}
}
lbl_15:
{
obj* x_168; obj* x_169; uint8 x_170; 
lean::dec(x_14);
x_168 = l_lean_ir_type2id___main(x_1);
x_169 = l_lean_ir_is__arith__ty___closed__1;
x_170 = lean::nat_dec_eq(x_168, x_169);
lean::dec(x_168);
if (x_170 == 0)
{
uint8 x_172; 
x_172 = 0;
return x_172;
}
else
{
obj* x_173; obj* x_174; uint8 x_175; 
x_173 = l_lean_ir_type2id___main(x_2);
x_174 = l_lean_ir_type2id___main(x_3);
x_175 = lean::nat_dec_eq(x_173, x_174);
lean::dec(x_174);
lean::dec(x_173);
if (x_175 == 0)
{
uint8 x_178; 
x_178 = 0;
return x_178;
}
else
{
uint8 x_179; 
x_179 = 1;
return x_179;
}
}
}
lbl_17:
{
obj* x_181; obj* x_182; uint8 x_183; 
lean::dec(x_16);
x_181 = l_lean_ir_type2id___main(x_1);
x_182 = l_lean_ir_is__arith__ty___closed__1;
x_183 = lean::nat_dec_eq(x_181, x_182);
lean::dec(x_181);
if (x_183 == 0)
{
uint8 x_185; 
x_185 = 0;
return x_185;
}
else
{
obj* x_186; obj* x_187; uint8 x_188; 
x_186 = l_lean_ir_type2id___main(x_2);
x_187 = l_lean_ir_type2id___main(x_3);
x_188 = lean::nat_dec_eq(x_186, x_187);
lean::dec(x_187);
if (x_188 == 0)
{
uint8 x_191; 
lean::dec(x_186);
x_191 = 0;
return x_191;
}
else
{
obj* x_192; uint8 x_193; 
x_192 = l_lean_ir_valid__assign__unop__types___closed__1;
x_193 = lean::nat_dec_eq(x_186, x_192);
lean::dec(x_186);
if (x_193 == 0)
{
uint8 x_195; 
x_195 = 0;
return x_195;
}
else
{
uint8 x_196; 
x_196 = 1;
return x_196;
}
}
}
}
}
}
obj* l_lean_ir_valid__assign__binop__types___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; uint8 x_6; uint8 x_7; uint8 x_8; obj* x_9; 
x_4 = lean::unbox(x_0);
x_5 = lean::unbox(x_1);
x_6 = lean::unbox(x_2);
x_7 = lean::unbox(x_3);
x_8 = l_lean_ir_valid__assign__binop__types(x_4, x_5, x_6, x_7);
x_9 = lean::box(x_8);
return x_9;
}
}
obj* _init_l_lean_ir_type__checker__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_ir_type__checker__m_run___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
x_6 = l_lean_ir_mk__context;
x_7 = lean::apply_2(x_0, x_5, x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
return x_8;
}
}
obj* l_lean_ir_type__checker__m_run(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_type__checker__m_run___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_ir_type__checker__m_run___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_type__checker__m_run___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_type__checker__m_run___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_type__checker__m_run(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_match__type___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("type mismatch, variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_match__type___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("` has type `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_match__type___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("`");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_match__type___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(", but is expected to have type `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_match__type___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_match__type(obj* x_0, uint8 x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = l_lean_ir_type2id___main(x_1);
x_6 = l_lean_ir_type2id___main(x_2);
x_7 = lean::nat_dec_eq(x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
if (x_7 == 0)
{
obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; 
x_10 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_11 = 0;
x_12 = l_lean_ir_match__type___closed__1;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_11);
x_14 = x_13;
x_15 = l_lean_ir_match__type___closed__2;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_11);
x_17 = x_16;
x_18 = l_lean_ir_type_to__format___main(x_1);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_11);
x_20 = x_19;
x_21 = l_lean_ir_match__type___closed__3;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_11);
x_23 = x_22;
x_24 = l_lean_ir_match__type___closed__4;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_11);
x_26 = x_25;
x_27 = l_lean_ir_type_to__format___main(x_2);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_11);
x_29 = x_28;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_21);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_11);
x_31 = x_30;
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::inc(x_4);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_4);
return x_34;
}
else
{
obj* x_36; obj* x_38; 
lean::dec(x_0);
x_36 = l_lean_ir_match__type___closed__5;
lean::inc(x_4);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_4);
return x_38;
}
}
}
obj* l_lean_ir_match__type___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; uint8 x_6; obj* x_7; 
x_5 = lean::unbox(x_1);
x_6 = lean::unbox(x_2);
x_7 = l_lean_ir_match__type(x_0, x_5, x_6, x_3, x_4);
lean::dec(x_3);
lean::dec(x_4);
return x_7;
}
}
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = l_lean_name_quick__lt___main(x_1, x_4);
x_8 = lean::unbox(x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = l_lean_name_quick__lt___main(x_4, x_1);
x_10 = lean::unbox(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::inc(x_5);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_5);
return x_12;
}
else
{
x_0 = x_6;
goto _start;
}
}
else
{
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_ir_get__type___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_ir_get__type___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("undefined variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_get__type(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_2, x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
x_4 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_5 = 0;
x_6 = l_lean_ir_get__type___closed__1;
x_7 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set_scalar(x_7, sizeof(void*)*2, x_5);
x_8 = x_7;
x_9 = l_lean_ir_match__type___closed__3;
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_5);
x_11 = x_10;
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::inc(x_2);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_2);
return x_14;
}
else
{
obj* x_16; obj* x_19; obj* x_21; 
lean::dec(x_0);
x_16 = lean::cnstr_get(x_3, 0);
lean::inc(x_16);
lean::dec(x_3);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::inc(x_2);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_2);
return x_21;
}
}
}
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_find___main___at_lean_ir_get__type___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_ir_get__type___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_ir_get__type___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_ir_get__type___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_get__type(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_ir_set__type___spec__3(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_6; obj* x_7; 
x_3 = 0;
x_4 = lean::box(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_4);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
x_24 = lean::box(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_24);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
x_49 = lean::box(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_49);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_set__type___spec__2(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbmap_insert___main___at_lean_ir_set__type___spec__1(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_set__type___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_set__type(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_3, x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = l_rbnode_insert___at_lean_ir_set__type___spec__2(x_3, x_0, x_1);
lean::dec(x_0);
x_7 = l_lean_ir_match__type___closed__5;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
obj* x_9; uint8 x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::unbox(x_9);
x_13 = l_lean_ir_match__type(x_0, x_12, x_1, x_2, x_3);
lean::dec(x_3);
return x_13;
}
}
}
obj* l_rbnode_ins___main___at_lean_ir_set__type___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_0, x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbnode_insert___at_lean_ir_set__type___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_rbnode_insert___at_lean_ir_set__type___spec__2(x_0, x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_ir_set__type___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_rbmap_insert___main___at_lean_ir_set__type___spec__1(x_0, x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_ir_set__type___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_set__type(x_0, x_4, x_2, x_3);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_lean_ir_check__type___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("type for variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_check__type___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("` is not available");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_check__type(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_3, x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
x_5 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_6 = 0;
x_7 = l_lean_ir_check__type___closed__1;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_6);
x_9 = x_8;
x_10 = l_lean_ir_check__type___closed__2;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_6);
x_12 = x_11;
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::inc(x_3);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_3);
return x_15;
}
else
{
obj* x_16; uint8 x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_4, 0);
lean::inc(x_16);
lean::dec(x_4);
x_19 = lean::unbox(x_16);
x_20 = l_lean_ir_match__type(x_0, x_19, x_1, x_2, x_3);
return x_20;
}
}
}
obj* l_lean_ir_check__type___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_check__type(x_0, x_4, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* _init_l_lean_ir_check__ne__type___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_check__ne__type___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("` must not have type `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_check__ne__type(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_3, x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
x_5 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_6 = 0;
x_7 = l_lean_ir_check__type___closed__1;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_6);
x_9 = x_8;
x_10 = l_lean_ir_check__type___closed__2;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_6);
x_12 = x_11;
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::inc(x_3);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_3);
return x_15;
}
else
{
obj* x_16; uint8 x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_16 = lean::cnstr_get(x_4, 0);
lean::inc(x_16);
lean::dec(x_4);
x_19 = lean::unbox(x_16);
x_20 = l_lean_ir_type2id___main(x_19);
x_21 = l_lean_ir_type2id___main(x_1);
x_22 = lean::nat_dec_eq(x_20, x_21);
lean::dec(x_21);
lean::dec(x_20);
if (x_22 == 0)
{
obj* x_26; obj* x_28; 
lean::dec(x_0);
x_26 = l_lean_ir_match__type___closed__5;
lean::inc(x_3);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_3);
return x_28;
}
else
{
obj* x_29; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; 
x_29 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_30 = 0;
x_31 = l_lean_ir_check__ne__type___closed__1;
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_30);
x_33 = x_32;
x_34 = l_lean_ir_check__ne__type___closed__2;
x_35 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_30);
x_36 = x_35;
x_37 = l_lean_ir_type_to__format___main(x_1);
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_30);
x_39 = x_38;
x_40 = l_lean_ir_match__type___closed__3;
x_41 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
lean::cnstr_set_scalar(x_41, sizeof(void*)*2, x_30);
x_42 = x_41;
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::inc(x_3);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_3);
return x_45;
}
}
}
}
obj* l_lean_ir_check__ne__type___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_check__ne__type(x_0, x_4, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* _init_l_lean_ir_invalid__literal___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid literal");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_ir_invalid__literal___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
}
}
obj* l_lean_ir_invalid__literal(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_invalid__literal___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_ir_invalid__literal___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_invalid__literal___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_invalid__literal___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_invalid__literal(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_literal_check(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = l_lean_ir_type2id___main(x_1);
x_5 = l_lean_ir_is__arith__ty___closed__1;
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_4);
if (x_6 == 0)
{
obj* x_8; obj* x_10; 
x_8 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
else
{
obj* x_11; obj* x_13; 
x_11 = l_lean_ir_match__type___closed__5;
lean::inc(x_3);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
}
case 1:
{
obj* x_14; obj* x_15; uint8 x_16; 
x_14 = l_lean_ir_type2id___main(x_1);
x_15 = l_lean_ir_valid__assign__unop__types___closed__1;
x_16 = lean::nat_dec_eq(x_14, x_15);
lean::dec(x_14);
if (x_16 == 0)
{
obj* x_18; obj* x_20; 
x_18 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_3);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_3);
return x_20;
}
else
{
obj* x_21; obj* x_23; 
x_21 = l_lean_ir_match__type___closed__5;
lean::inc(x_3);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_3);
return x_23;
}
}
case 2:
{
obj* x_24; uint8 x_25; obj* x_26; uint8 x_27; 
x_24 = lean::cnstr_get(x_0, 0);
x_25 = l_lean_ir_is__nonfloat__arith__ty(x_1);
x_26 = l_int_zero;
x_27 = lean::int_dec_lt(x_24, x_26);
if (x_25 == 0)
{
obj* x_28; 
x_28 = l_lean_ir_invalid__literal___rarg___closed__1;
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; 
x_29 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_31 = x_28;
} else {
 lean::inc(x_29);
 lean::dec(x_28);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
lean::inc(x_3);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_3);
return x_34;
}
else
{
if (x_27 == 0)
{
obj* x_35; obj* x_37; 
x_35 = l_lean_ir_match__type___closed__5;
lean::inc(x_3);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_3);
return x_37;
}
else
{
uint8 x_38; 
x_38 = l_lean_ir_is__signed__arith__ty(x_1);
if (x_38 == 0)
{
obj* x_40; 
lean::inc(x_3);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_28);
lean::cnstr_set(x_40, 1, x_3);
return x_40;
}
else
{
obj* x_41; obj* x_43; 
x_41 = l_lean_ir_match__type___closed__5;
lean::inc(x_3);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_3);
return x_43;
}
}
}
}
else
{
if (x_27 == 0)
{
obj* x_44; obj* x_46; 
x_44 = l_lean_ir_match__type___closed__5;
lean::inc(x_3);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_3);
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_lean_ir_is__signed__arith__ty(x_1);
if (x_47 == 0)
{
obj* x_48; obj* x_50; 
x_48 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_3);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_3);
return x_50;
}
else
{
obj* x_51; obj* x_53; 
x_51 = l_lean_ir_match__type___closed__5;
lean::inc(x_3);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_3);
return x_53;
}
}
}
}
default:
{
obj* x_54; obj* x_55; uint8 x_56; 
x_54 = l_lean_ir_type2id___main(x_1);
x_55 = l_lean_ir_is__nonfloat__arith__ty___closed__2;
x_56 = lean::nat_dec_eq(x_54, x_55);
if (x_56 == 0)
{
obj* x_57; uint8 x_58; 
x_57 = l_lean_ir_is__nonfloat__arith__ty___closed__1;
x_58 = lean::nat_dec_eq(x_54, x_57);
lean::dec(x_54);
if (x_58 == 0)
{
obj* x_60; obj* x_62; 
x_60 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_3);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_3);
return x_62;
}
else
{
obj* x_63; obj* x_65; 
x_63 = l_lean_ir_match__type___closed__5;
lean::inc(x_3);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_3);
return x_65;
}
}
else
{
obj* x_67; obj* x_69; 
lean::dec(x_54);
x_67 = l_lean_ir_match__type___closed__5;
lean::inc(x_3);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_3);
return x_69;
}
}
}
}
}
obj* l_lean_ir_literal_check___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_literal_check(x_0, x_4, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* _init_l_lean_ir_get__decl___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("unknown function `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_get__decl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_release(x_1, 1);
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
lean::inc(x_0);
x_7 = lean::apply_1(x_3, x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; 
x_8 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_0);
x_9 = 0;
x_10 = l_lean_ir_get__decl___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l_lean_ir_match__type___closed__3;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::inc(x_2);
if (lean::is_scalar(x_5)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_5;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_2);
return x_18;
}
else
{
obj* x_20; obj* x_23; obj* x_25; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_7, 0);
lean::inc(x_20);
lean::dec(x_7);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::inc(x_2);
if (lean::is_scalar(x_5)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_5;
}
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_2);
return x_25;
}
}
}
obj* l_lean_ir_get__decl___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_get__decl(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_set__result__types___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_set__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_set__result__types___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_set__result__types___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_ir_set__result__types(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_set__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_set__result__types___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_set__result__types(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_ir_instr_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; uint8 x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_8 = l_lean_ir_set__type(x_5, x_7, x_1, x_2);
lean::dec(x_1);
x_3 = x_8;
goto lbl_4;
}
case 1:
{
obj* x_10; uint8 x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_13 = l_lean_ir_set__type(x_10, x_12, x_1, x_2);
lean::dec(x_1);
x_3 = x_13;
goto lbl_4;
}
case 2:
{
obj* x_15; uint8 x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_18 = l_lean_ir_set__type(x_15, x_17, x_1, x_2);
lean::dec(x_1);
x_3 = x_18;
goto lbl_4;
}
case 3:
{
obj* x_20; uint8 x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_23 = l_lean_ir_set__type(x_20, x_22, x_1, x_2);
lean::dec(x_1);
x_3 = x_23;
goto lbl_4;
}
case 4:
{
obj* x_26; obj* x_27; 
lean::dec(x_1);
x_26 = l_lean_ir_match__type___closed__5;
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_2);
x_3 = x_27;
goto lbl_4;
}
case 5:
{
obj* x_28; obj* x_30; obj* x_33; obj* x_35; 
x_28 = lean::cnstr_get(x_0, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::inc(x_1);
x_33 = l_lean_ir_get__decl(x_30, x_1, x_2);
lean::dec(x_2);
x_35 = lean::cnstr_get(x_33, 0);
lean::inc(x_35);
if (lean::obj_tag(x_35) == 0)
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_1);
lean::dec(x_28);
x_39 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_44 = x_35;
} else {
 lean::inc(x_42);
 lean::dec(x_35);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_42);
if (lean::is_scalar(x_41)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_41;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_39);
x_3 = x_46;
goto lbl_4;
}
else
{
obj* x_47; obj* x_50; obj* x_53; obj* x_55; uint8 x_58; obj* x_59; 
x_47 = lean::cnstr_get(x_33, 1);
lean::inc(x_47);
lean::dec(x_33);
x_50 = lean::cnstr_get(x_35, 0);
lean::inc(x_50);
lean::dec(x_35);
x_53 = l_lean_ir_decl_header___main(x_50);
lean::dec(x_50);
x_55 = lean::cnstr_get(x_53, 2);
lean::inc(x_55);
lean::dec(x_53);
x_58 = lean::unbox(x_55);
x_59 = l_lean_ir_set__type(x_28, x_58, x_1, x_47);
lean::dec(x_1);
x_3 = x_59;
goto lbl_4;
}
}
case 7:
{
obj* x_62; obj* x_63; 
lean::dec(x_1);
x_62 = l_lean_ir_match__type___closed__5;
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_2);
x_3 = x_63;
goto lbl_4;
}
case 9:
{
obj* x_65; obj* x_66; 
lean::dec(x_1);
x_65 = l_lean_ir_match__type___closed__5;
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_2);
x_3 = x_66;
goto lbl_4;
}
case 10:
{
obj* x_67; uint8 x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_0, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_70 = l_lean_ir_set__type(x_67, x_69, x_1, x_2);
lean::dec(x_1);
x_3 = x_70;
goto lbl_4;
}
case 15:
{
obj* x_73; obj* x_74; 
lean::dec(x_1);
x_73 = l_lean_ir_match__type___closed__5;
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_2);
x_3 = x_74;
goto lbl_4;
}
default:
{
obj* x_75; uint8 x_77; obj* x_78; 
x_75 = lean::cnstr_get(x_0, 0);
lean::inc(x_75);
x_77 = 11;
x_78 = l_lean_ir_set__type(x_75, x_77, x_1, x_2);
lean::dec(x_1);
x_3 = x_78;
goto lbl_4;
}
}
lbl_4:
{
obj* x_80; 
x_80 = lean::cnstr_get(x_3, 0);
lean::inc(x_80);
if (lean::obj_tag(x_80) == 0)
{
obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_88; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_82 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_84 = x_3;
} else {
 lean::inc(x_82);
 lean::dec(x_3);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 x_87 = x_80;
} else {
 lean::inc(x_85);
 lean::dec(x_80);
 x_87 = lean::box(0);
}
x_88 = l_lean_ir_instr_to__format___main(x_0);
x_89 = 0;
x_90 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_91 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_88);
lean::cnstr_set_scalar(x_91, sizeof(void*)*2, x_89);
x_92 = x_91;
x_93 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_94 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_93);
lean::cnstr_set_scalar(x_94, sizeof(void*)*2, x_89);
x_95 = x_94;
x_96 = lean::box(1);
x_97 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_97, 0, x_95);
lean::cnstr_set(x_97, 1, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*2, x_89);
x_98 = x_97;
x_99 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_85);
lean::cnstr_set_scalar(x_99, sizeof(void*)*2, x_89);
x_100 = x_99;
if (lean::is_scalar(x_87)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_87;
}
lean::cnstr_set(x_101, 0, x_100);
if (lean::is_scalar(x_84)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_84;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_82);
return x_102;
}
else
{
obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_0);
x_104 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_106 = x_3;
} else {
 lean::inc(x_104);
 lean::dec(x_3);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_80);
lean::cnstr_set(x_107, 1, x_104);
return x_107;
}
}
}
}
obj* l_lean_ir_phi_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_6 = l_lean_ir_set__type(x_3, x_5, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_14 = x_7;
} else {
 lean::inc(x_12);
 lean::dec(x_7);
 x_14 = lean::box(0);
}
x_15 = l_lean_ir_phi_to__format___main(x_0);
x_16 = 0;
x_17 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_15);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_16);
x_19 = x_18;
x_20 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_16);
x_22 = x_21;
x_23 = lean::box(1);
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_16);
x_25 = x_24;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_12);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_16);
x_27 = x_26;
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_27);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_9);
return x_29;
}
else
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_0);
x_31 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_33 = x_6;
} else {
 lean::inc(x_31);
 lean::dec(x_6);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_7);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
}
obj* l_lean_ir_phi_infer__types___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_phi_infer__types(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_arg_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
lean::dec(x_0);
x_7 = l_lean_ir_set__type(x_3, x_5, x_1, x_2);
return x_7;
}
}
obj* l_lean_ir_arg_infer__types___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_arg_infer__types(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_match__type___closed__5;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_phi_infer__types(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_23;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_instr_infer__types(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_block_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_1);
x_9 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_11 = x_5;
} else {
 lean::inc(x_9);
 lean::dec(x_5);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_14 = x_6;
} else {
 lean::inc(x_12);
 lean::dec(x_6);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_18 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_15);
x_19 = 0;
x_20 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_19);
x_22 = x_21;
x_23 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_19);
x_25 = x_24;
x_26 = lean::box(1);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_19);
x_28 = x_27;
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_12);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_19);
x_30 = x_29;
if (lean::is_scalar(x_14)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_14;
}
lean::cnstr_set(x_31, 0, x_30);
if (lean::is_scalar(x_11)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_11;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_9);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_6);
x_34 = lean::cnstr_get(x_5, 1);
lean::inc(x_34);
lean::dec(x_5);
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__2(x_37, x_1, x_34);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_51; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_44 = x_39;
} else {
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_0, 0);
lean::inc(x_48);
lean::dec(x_0);
x_51 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_48);
x_52 = 0;
x_53 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_52);
x_55 = x_54;
x_56 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_52);
x_58 = x_57;
x_59 = lean::box(1);
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_52);
x_61 = x_60;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_45);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_52);
x_63 = x_62;
if (lean::is_scalar(x_47)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_47;
}
lean::cnstr_set(x_64, 0, x_63);
if (lean::is_scalar(x_44)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_44;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_42);
return x_65;
}
else
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_0);
x_67 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_69 = x_39;
} else {
 lean::inc(x_67);
 lean::dec(x_39);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_40);
lean::cnstr_set(x_70, 1, x_67);
return x_70;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_match__type___closed__5;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_arg_infer__types(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_23;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_block_infer__types(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_decl_infer__types___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_16; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1(x_13, x_1, x_2);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_29; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_10);
lean::dec(x_1);
x_20 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_22 = x_15;
} else {
 lean::inc(x_20);
 lean::dec(x_15);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_25 = x_16;
} else {
 lean::inc(x_23);
 lean::dec(x_16);
 x_25 = lean::box(0);
}
x_26 = lean::cnstr_get(x_8, 0);
lean::inc(x_26);
lean::dec(x_8);
x_29 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_26);
x_30 = 0;
x_31 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_30);
x_33 = x_32;
x_34 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_35 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_30);
x_36 = x_35;
x_37 = lean::box(1);
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_30);
x_39 = x_38;
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_23);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_30);
x_41 = x_40;
if (lean::is_scalar(x_25)) {
 x_42 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_42 = x_25;
}
lean::cnstr_set(x_42, 0, x_41);
if (lean::is_scalar(x_22)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_22;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_20);
return x_43;
}
else
{
obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_16);
x_45 = lean::cnstr_get(x_15, 1);
lean::inc(x_45);
lean::dec(x_15);
x_48 = l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__2(x_10, x_1, x_45);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
if (lean::obj_tag(x_49) == 0)
{
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_51 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_53 = x_48;
} else {
 lean::inc(x_51);
 lean::dec(x_48);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 x_56 = x_49;
} else {
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_8, 0);
lean::inc(x_57);
lean::dec(x_8);
x_60 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_57);
x_61 = 0;
x_62 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_60);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_61);
x_64 = x_63;
x_65 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_66 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set(x_66, 1, x_65);
lean::cnstr_set_scalar(x_66, sizeof(void*)*2, x_61);
x_67 = x_66;
x_68 = lean::box(1);
x_69 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_68);
lean::cnstr_set_scalar(x_69, sizeof(void*)*2, x_61);
x_70 = x_69;
x_71 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_54);
lean::cnstr_set_scalar(x_71, sizeof(void*)*2, x_61);
x_72 = x_71;
if (lean::is_scalar(x_56)) {
 x_73 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_73 = x_56;
}
lean::cnstr_set(x_73, 0, x_72);
if (lean::is_scalar(x_53)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_53;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_51);
return x_74;
}
else
{
obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_8);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 x_76 = x_49;
} else {
 lean::dec(x_49);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_79 = x_48;
} else {
 lean::inc(x_77);
 lean::dec(x_48);
 x_79 = lean::box(0);
}
lean::inc(x_77);
if (lean::is_scalar(x_76)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_76;
}
lean::cnstr_set(x_81, 0, x_77);
if (lean::is_scalar(x_79)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_79;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_77);
return x_82;
}
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_decl_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_decl_infer__types___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_infer__types(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_9; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_decl_infer__types), 3, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = l_lean_ir_decl_header___main(x_0);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_4, 2);
lean::inc(x_6);
lean::dec(x_4);
x_9 = l_lean_ir_type__checker__m_run___rarg(x_3, x_1, x_6);
lean::dec(x_6);
return x_9;
}
}
obj* l_lean_ir_infer__types___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_infer__types(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_ir_check__arg__types___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("unexpected number of arguments");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_ir_check__arg__types___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_lean_ir_check__arg__types___main___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_0);
x_9 = l_lean_ir_check__arg__types___main___closed__1;
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_21; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
x_19 = l_lean_ir_check__type(x_11, x_18, x_2, x_3);
lean::dec(x_3);
x_21 = lean::cnstr_get(x_19, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_13);
x_24 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_26 = x_19;
} else {
 lean::inc(x_24);
 lean::dec(x_19);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_29 = x_21;
} else {
 lean::inc(x_27);
 lean::dec(x_21);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_27);
if (lean::is_scalar(x_26)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_26;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_24);
return x_31;
}
else
{
obj* x_33; 
lean::dec(x_21);
x_33 = lean::cnstr_get(x_19, 1);
lean::inc(x_33);
lean::dec(x_19);
x_0 = x_13;
x_1 = x_17;
x_3 = x_33;
goto _start;
}
}
}
}
}
obj* l_lean_ir_check__arg__types___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_check__arg__types___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_ir_check__arg__types(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_check__arg__types___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_ir_check__arg__types___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_check__arg__types(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_match__type___closed__5;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; uint8 x_10; obj* x_11; obj* x_13; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = 11;
x_11 = l_lean_ir_check__type(x_5, x_10, x_1, x_2);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_7);
x_16 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
} else {
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_21 = x_13;
} else {
 lean::inc(x_19);
 lean::dec(x_13);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_19);
if (lean::is_scalar(x_18)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_18;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_16);
return x_23;
}
else
{
obj* x_25; 
lean::dec(x_13);
x_25 = lean::cnstr_get(x_11, 1);
lean::inc(x_25);
lean::dec(x_11);
x_0 = x_7;
x_2 = x_25;
goto _start;
}
}
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid closure, arguments must have type object");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; 
x_3 = l_lean_ir_match__type___closed__5;
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_6 = lean::cnstr_get(x_0, 0);
x_7 = lean::cnstr_get(x_0, 1);
x_8 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
x_9 = l_lean_ir_type2id___main(x_8);
x_10 = l_lean_ir_valid__assign__unop__types___closed__1;
x_11 = lean::nat_dec_eq(x_9, x_10);
lean::dec(x_9);
if (x_11 == 0)
{
obj* x_13; obj* x_15; 
x_13 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1;
lean::inc(x_2);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_2);
return x_15;
}
else
{
x_0 = x_7;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_match__type___closed__5;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; uint8 x_10; obj* x_11; obj* x_13; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = 11;
x_11 = l_lean_ir_check__type(x_5, x_10, x_1, x_2);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_7);
x_16 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
} else {
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_21 = x_13;
} else {
 lean::inc(x_19);
 lean::dec(x_13);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_19);
if (lean::is_scalar(x_18)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_18;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_16);
return x_23;
}
else
{
obj* x_25; 
lean::dec(x_13);
x_25 = lean::cnstr_get(x_11, 1);
lean::inc(x_25);
lean::dec(x_11);
x_0 = x_7;
x_2 = x_25;
goto _start;
}
}
}
}
obj* _init_l_lean_ir_instr_check___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid assignment");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_ir_instr_check___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid unary operation");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_ir_instr_check___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid binary operation");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_ir_instr_check___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("too many arguments");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_ir_instr_check___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid scalar array");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_ir_instr_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_5; obj* x_6; obj* x_8; obj* x_11; 
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = l_lean_ir_get__type(x_6, x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_15 = x_8;
} else {
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_18 = x_11;
} else {
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
x_3 = x_20;
goto lbl_4;
}
else
{
obj* x_21; obj* x_23; obj* x_24; obj* x_27; uint8 x_28; obj* x_29; uint8 x_30; 
x_21 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_23 = x_8;
} else {
 lean::inc(x_21);
 lean::dec(x_8);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_11, 0);
lean::inc(x_24);
lean::dec(x_11);
x_27 = l_lean_ir_type2id___main(x_5);
x_28 = lean::unbox(x_24);
x_29 = l_lean_ir_type2id___main(x_28);
x_30 = lean::nat_dec_eq(x_27, x_29);
lean::dec(x_29);
lean::dec(x_27);
if (x_30 == 0)
{
obj* x_33; obj* x_34; 
x_33 = l_lean_ir_instr_check___closed__1;
if (lean::is_scalar(x_23)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_23;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_21);
x_3 = x_34;
goto lbl_4;
}
else
{
obj* x_35; obj* x_36; 
x_35 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_23)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_23;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_21);
x_3 = x_36;
goto lbl_4;
}
}
}
case 1:
{
uint8 x_37; obj* x_38; obj* x_40; 
x_37 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_38 = lean::cnstr_get(x_0, 1);
lean::inc(x_38);
x_40 = l_lean_ir_literal_check(x_38, x_37, x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_38);
x_3 = x_40;
goto lbl_4;
}
case 2:
{
uint8 x_44; uint8 x_45; obj* x_46; obj* x_48; obj* x_51; 
x_44 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_45 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2 + 1);
x_46 = lean::cnstr_get(x_0, 1);
lean::inc(x_46);
x_48 = l_lean_ir_get__type(x_46, x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
if (lean::obj_tag(x_51) == 0)
{
obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; 
x_53 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_55 = x_48;
} else {
 lean::inc(x_53);
 lean::dec(x_48);
 x_55 = lean::box(0);
}
x_56 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_58 = x_51;
} else {
 lean::inc(x_56);
 lean::dec(x_51);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_56);
if (lean::is_scalar(x_55)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_55;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_53);
x_3 = x_60;
goto lbl_4;
}
else
{
obj* x_61; obj* x_63; obj* x_64; uint8 x_67; uint8 x_68; 
x_61 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_set(x_48, 1, lean::box(0));
 x_63 = x_48;
} else {
 lean::inc(x_61);
 lean::dec(x_48);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_51, 0);
lean::inc(x_64);
lean::dec(x_51);
x_67 = lean::unbox(x_64);
x_68 = l_lean_ir_valid__assign__unop__types(x_45, x_44, x_67);
if (x_68 == 0)
{
obj* x_69; obj* x_70; 
x_69 = l_lean_ir_instr_check___closed__2;
if (lean::is_scalar(x_63)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_63;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_61);
x_3 = x_70;
goto lbl_4;
}
else
{
obj* x_71; obj* x_72; 
x_71 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_63)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_63;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_61);
x_3 = x_72;
goto lbl_4;
}
}
}
case 3:
{
uint8 x_73; uint8 x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_81; 
x_73 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_74 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3 + 1);
x_75 = lean::cnstr_get(x_0, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_0, 2);
lean::inc(x_77);
x_79 = l_lean_ir_get__type(x_75, x_1, x_2);
lean::dec(x_2);
x_81 = lean::cnstr_get(x_79, 0);
lean::inc(x_81);
if (lean::obj_tag(x_81) == 0)
{
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_1);
lean::dec(x_77);
x_85 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 x_87 = x_79;
} else {
 lean::inc(x_85);
 lean::dec(x_79);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_81, 0);
if (lean::is_exclusive(x_81)) {
 x_90 = x_81;
} else {
 lean::inc(x_88);
 lean::dec(x_81);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
if (lean::is_scalar(x_87)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_87;
}
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_85);
x_3 = x_92;
goto lbl_4;
}
else
{
obj* x_93; obj* x_96; obj* x_99; obj* x_102; 
x_93 = lean::cnstr_get(x_79, 1);
lean::inc(x_93);
lean::dec(x_79);
x_96 = lean::cnstr_get(x_81, 0);
lean::inc(x_96);
lean::dec(x_81);
x_99 = l_lean_ir_get__type(x_77, x_1, x_93);
lean::dec(x_93);
lean::dec(x_1);
x_102 = lean::cnstr_get(x_99, 0);
lean::inc(x_102);
if (lean::obj_tag(x_102) == 0)
{
obj* x_105; obj* x_107; obj* x_108; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_96);
x_105 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 x_107 = x_99;
} else {
 lean::inc(x_105);
 lean::dec(x_99);
 x_107 = lean::box(0);
}
x_108 = lean::cnstr_get(x_102, 0);
if (lean::is_exclusive(x_102)) {
 x_110 = x_102;
} else {
 lean::inc(x_108);
 lean::dec(x_102);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
if (lean::is_scalar(x_107)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_107;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_105);
x_3 = x_112;
goto lbl_4;
}
else
{
obj* x_113; obj* x_115; obj* x_116; uint8 x_119; uint8 x_120; uint8 x_121; 
x_113 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_set(x_99, 1, lean::box(0));
 x_115 = x_99;
} else {
 lean::inc(x_113);
 lean::dec(x_99);
 x_115 = lean::box(0);
}
x_116 = lean::cnstr_get(x_102, 0);
lean::inc(x_116);
lean::dec(x_102);
x_119 = lean::unbox(x_96);
x_120 = lean::unbox(x_116);
x_121 = l_lean_ir_valid__assign__binop__types(x_74, x_73, x_119, x_120);
if (x_121 == 0)
{
obj* x_122; obj* x_123; 
x_122 = l_lean_ir_instr_check___closed__3;
if (lean::is_scalar(x_115)) {
 x_123 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_123 = x_115;
}
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_113);
x_3 = x_123;
goto lbl_4;
}
else
{
obj* x_124; obj* x_125; 
x_124 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_115)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_115;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_113);
x_3 = x_125;
goto lbl_4;
}
}
}
}
case 4:
{
obj* x_126; uint8 x_128; obj* x_129; 
x_126 = lean::cnstr_get(x_0, 0);
lean::inc(x_126);
x_128 = 11;
x_129 = l_lean_ir_check__type(x_126, x_128, x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_3 = x_129;
goto lbl_4;
}
case 5:
{
obj* x_132; obj* x_134; obj* x_137; obj* x_139; 
x_132 = lean::cnstr_get(x_0, 1);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_0, 2);
lean::inc(x_134);
lean::inc(x_1);
x_137 = l_lean_ir_get__decl(x_132, x_1, x_2);
lean::dec(x_2);
x_139 = lean::cnstr_get(x_137, 0);
lean::inc(x_139);
if (lean::obj_tag(x_139) == 0)
{
obj* x_143; obj* x_145; obj* x_146; obj* x_148; obj* x_149; obj* x_150; 
lean::dec(x_134);
lean::dec(x_1);
x_143 = lean::cnstr_get(x_137, 1);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 x_145 = x_137;
} else {
 lean::inc(x_143);
 lean::dec(x_137);
 x_145 = lean::box(0);
}
x_146 = lean::cnstr_get(x_139, 0);
if (lean::is_exclusive(x_139)) {
 x_148 = x_139;
} else {
 lean::inc(x_146);
 lean::dec(x_139);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_146);
if (lean::is_scalar(x_145)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_145;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_143);
x_3 = x_150;
goto lbl_4;
}
else
{
obj* x_151; obj* x_154; obj* x_157; obj* x_159; obj* x_162; 
x_151 = lean::cnstr_get(x_137, 1);
lean::inc(x_151);
lean::dec(x_137);
x_154 = lean::cnstr_get(x_139, 0);
lean::inc(x_154);
lean::dec(x_139);
x_157 = l_lean_ir_decl_header___main(x_154);
lean::dec(x_154);
x_159 = lean::cnstr_get(x_157, 1);
lean::inc(x_159);
lean::dec(x_157);
x_162 = l_lean_ir_check__arg__types___main(x_134, x_159, x_1, x_151);
lean::dec(x_1);
lean::dec(x_159);
x_3 = x_162;
goto lbl_4;
}
}
case 6:
{
obj* x_166; obj* x_167; 
lean::dec(x_1);
x_166 = l_lean_ir_match__type___closed__5;
x_167 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_2);
x_3 = x_167;
goto lbl_4;
}
case 7:
{
obj* x_168; obj* x_170; uint8 x_172; obj* x_173; obj* x_175; 
x_168 = lean::cnstr_get(x_0, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_0, 1);
lean::inc(x_170);
x_172 = 11;
x_173 = l_lean_ir_check__type(x_168, x_172, x_1, x_2);
lean::dec(x_2);
x_175 = lean::cnstr_get(x_173, 0);
lean::inc(x_175);
if (lean::obj_tag(x_175) == 0)
{
obj* x_179; obj* x_181; obj* x_182; obj* x_184; obj* x_185; obj* x_186; 
lean::dec(x_1);
lean::dec(x_170);
x_179 = lean::cnstr_get(x_173, 1);
if (lean::is_exclusive(x_173)) {
 lean::cnstr_release(x_173, 0);
 x_181 = x_173;
} else {
 lean::inc(x_179);
 lean::dec(x_173);
 x_181 = lean::box(0);
}
x_182 = lean::cnstr_get(x_175, 0);
if (lean::is_exclusive(x_175)) {
 x_184 = x_175;
} else {
 lean::inc(x_182);
 lean::dec(x_175);
 x_184 = lean::box(0);
}
if (lean::is_scalar(x_184)) {
 x_185 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_185 = x_184;
}
lean::cnstr_set(x_185, 0, x_182);
if (lean::is_scalar(x_181)) {
 x_186 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_186 = x_181;
}
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_179);
x_3 = x_186;
goto lbl_4;
}
else
{
obj* x_188; obj* x_191; 
lean::dec(x_175);
x_188 = lean::cnstr_get(x_173, 1);
lean::inc(x_188);
lean::dec(x_173);
x_191 = l_lean_ir_check__type(x_170, x_172, x_1, x_188);
lean::dec(x_188);
lean::dec(x_1);
x_3 = x_191;
goto lbl_4;
}
}
case 8:
{
obj* x_194; uint8 x_196; obj* x_197; 
x_194 = lean::cnstr_get(x_0, 1);
lean::inc(x_194);
x_196 = 11;
x_197 = l_lean_ir_check__type(x_194, x_196, x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_3 = x_197;
goto lbl_4;
}
case 9:
{
obj* x_200; obj* x_202; uint8 x_204; obj* x_205; obj* x_207; 
x_200 = lean::cnstr_get(x_0, 0);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_0, 1);
lean::inc(x_202);
x_204 = 11;
x_205 = l_lean_ir_check__type(x_200, x_204, x_1, x_2);
lean::dec(x_2);
x_207 = lean::cnstr_get(x_205, 0);
lean::inc(x_207);
if (lean::obj_tag(x_207) == 0)
{
obj* x_211; obj* x_213; obj* x_214; obj* x_216; obj* x_217; obj* x_218; 
lean::dec(x_202);
lean::dec(x_1);
x_211 = lean::cnstr_get(x_205, 1);
if (lean::is_exclusive(x_205)) {
 lean::cnstr_release(x_205, 0);
 x_213 = x_205;
} else {
 lean::inc(x_211);
 lean::dec(x_205);
 x_213 = lean::box(0);
}
x_214 = lean::cnstr_get(x_207, 0);
if (lean::is_exclusive(x_207)) {
 x_216 = x_207;
} else {
 lean::inc(x_214);
 lean::dec(x_207);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_214);
if (lean::is_scalar(x_213)) {
 x_218 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_218 = x_213;
}
lean::cnstr_set(x_218, 0, x_217);
lean::cnstr_set(x_218, 1, x_211);
x_3 = x_218;
goto lbl_4;
}
else
{
obj* x_220; obj* x_223; 
lean::dec(x_207);
x_220 = lean::cnstr_get(x_205, 1);
lean::inc(x_220);
lean::dec(x_205);
x_223 = l_lean_ir_check__ne__type(x_202, x_204, x_1, x_220);
lean::dec(x_220);
lean::dec(x_1);
x_3 = x_223;
goto lbl_4;
}
}
case 10:
{
obj* x_226; obj* x_228; uint8 x_230; obj* x_231; obj* x_233; 
x_226 = lean::cnstr_get(x_0, 0);
lean::inc(x_226);
x_228 = lean::cnstr_get(x_0, 1);
lean::inc(x_228);
x_230 = 11;
x_231 = l_lean_ir_check__type(x_228, x_230, x_1, x_2);
lean::dec(x_2);
x_233 = lean::cnstr_get(x_231, 0);
lean::inc(x_233);
if (lean::obj_tag(x_233) == 0)
{
obj* x_237; obj* x_239; obj* x_240; obj* x_242; obj* x_243; obj* x_244; 
lean::dec(x_1);
lean::dec(x_226);
x_237 = lean::cnstr_get(x_231, 1);
if (lean::is_exclusive(x_231)) {
 lean::cnstr_release(x_231, 0);
 x_239 = x_231;
} else {
 lean::inc(x_237);
 lean::dec(x_231);
 x_239 = lean::box(0);
}
x_240 = lean::cnstr_get(x_233, 0);
if (lean::is_exclusive(x_233)) {
 x_242 = x_233;
} else {
 lean::inc(x_240);
 lean::dec(x_233);
 x_242 = lean::box(0);
}
if (lean::is_scalar(x_242)) {
 x_243 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_243 = x_242;
}
lean::cnstr_set(x_243, 0, x_240);
if (lean::is_scalar(x_239)) {
 x_244 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_244 = x_239;
}
lean::cnstr_set(x_244, 0, x_243);
lean::cnstr_set(x_244, 1, x_237);
x_3 = x_244;
goto lbl_4;
}
else
{
obj* x_246; obj* x_249; 
lean::dec(x_233);
x_246 = lean::cnstr_get(x_231, 1);
lean::inc(x_246);
lean::dec(x_231);
x_249 = l_lean_ir_check__ne__type(x_226, x_230, x_1, x_246);
lean::dec(x_246);
lean::dec(x_1);
x_3 = x_249;
goto lbl_4;
}
}
case 11:
{
obj* x_252; obj* x_254; obj* x_257; obj* x_258; 
x_252 = lean::cnstr_get(x_0, 1);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_0, 2);
lean::inc(x_254);
lean::inc(x_254);
x_257 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1(x_254, x_1, x_2);
x_258 = lean::cnstr_get(x_257, 0);
lean::inc(x_258);
if (lean::obj_tag(x_258) == 0)
{
obj* x_263; obj* x_265; obj* x_266; obj* x_268; obj* x_269; obj* x_270; 
lean::dec(x_1);
lean::dec(x_252);
lean::dec(x_254);
x_263 = lean::cnstr_get(x_257, 1);
if (lean::is_exclusive(x_257)) {
 lean::cnstr_release(x_257, 0);
 x_265 = x_257;
} else {
 lean::inc(x_263);
 lean::dec(x_257);
 x_265 = lean::box(0);
}
x_266 = lean::cnstr_get(x_258, 0);
if (lean::is_exclusive(x_258)) {
 x_268 = x_258;
} else {
 lean::inc(x_266);
 lean::dec(x_258);
 x_268 = lean::box(0);
}
if (lean::is_scalar(x_268)) {
 x_269 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_269 = x_268;
}
lean::cnstr_set(x_269, 0, x_266);
if (lean::is_scalar(x_265)) {
 x_270 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_270 = x_265;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_263);
x_3 = x_270;
goto lbl_4;
}
else
{
obj* x_272; obj* x_276; obj* x_278; 
lean::dec(x_258);
x_272 = lean::cnstr_get(x_257, 1);
lean::inc(x_272);
lean::dec(x_257);
lean::inc(x_1);
x_276 = l_lean_ir_get__decl(x_252, x_1, x_272);
lean::dec(x_272);
x_278 = lean::cnstr_get(x_276, 0);
lean::inc(x_278);
if (lean::obj_tag(x_278) == 0)
{
obj* x_282; obj* x_284; obj* x_285; obj* x_287; obj* x_288; obj* x_289; 
lean::dec(x_1);
lean::dec(x_254);
x_282 = lean::cnstr_get(x_276, 1);
if (lean::is_exclusive(x_276)) {
 lean::cnstr_release(x_276, 0);
 x_284 = x_276;
} else {
 lean::inc(x_282);
 lean::dec(x_276);
 x_284 = lean::box(0);
}
x_285 = lean::cnstr_get(x_278, 0);
if (lean::is_exclusive(x_278)) {
 x_287 = x_278;
} else {
 lean::inc(x_285);
 lean::dec(x_278);
 x_287 = lean::box(0);
}
if (lean::is_scalar(x_287)) {
 x_288 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_288 = x_287;
}
lean::cnstr_set(x_288, 0, x_285);
if (lean::is_scalar(x_284)) {
 x_289 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_289 = x_284;
}
lean::cnstr_set(x_289, 0, x_288);
lean::cnstr_set(x_289, 1, x_282);
x_3 = x_289;
goto lbl_4;
}
else
{
obj* x_290; obj* x_292; obj* x_293; obj* x_296; obj* x_297; obj* x_299; obj* x_301; obj* x_304; uint8 x_305; 
x_290 = lean::cnstr_get(x_276, 1);
if (lean::is_exclusive(x_276)) {
 lean::cnstr_release(x_276, 0);
 lean::cnstr_set(x_276, 1, lean::box(0));
 x_292 = x_276;
} else {
 lean::inc(x_290);
 lean::dec(x_276);
 x_292 = lean::box(0);
}
x_293 = lean::cnstr_get(x_278, 0);
lean::inc(x_293);
lean::dec(x_278);
x_296 = lean::mk_nat_obj(0u);
x_297 = l_list_length__aux___main___rarg(x_254, x_296);
lean::dec(x_254);
x_299 = l_lean_ir_decl_header___main(x_293);
lean::dec(x_293);
x_301 = lean::cnstr_get(x_299, 1);
lean::inc(x_301);
lean::dec(x_299);
x_304 = l_list_length__aux___main___rarg(x_301, x_296);
x_305 = lean::nat_dec_le(x_297, x_304);
lean::dec(x_304);
lean::dec(x_297);
if (x_305 == 0)
{
obj* x_310; obj* x_311; 
lean::dec(x_1);
lean::dec(x_301);
x_310 = l_lean_ir_instr_check___closed__4;
if (lean::is_scalar(x_292)) {
 x_311 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_311 = x_292;
}
lean::cnstr_set(x_311, 0, x_310);
lean::cnstr_set(x_311, 1, x_290);
x_3 = x_311;
goto lbl_4;
}
else
{
obj* x_313; 
lean::dec(x_292);
x_313 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2(x_301, x_1, x_290);
lean::dec(x_290);
lean::dec(x_1);
lean::dec(x_301);
x_3 = x_313;
goto lbl_4;
}
}
}
}
case 12:
{
obj* x_317; obj* x_319; 
x_317 = lean::cnstr_get(x_0, 1);
lean::inc(x_317);
x_319 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3(x_317, x_1, x_2);
lean::dec(x_1);
x_3 = x_319;
goto lbl_4;
}
case 13:
{
obj* x_321; obj* x_323; uint8 x_325; obj* x_326; obj* x_328; 
x_321 = lean::cnstr_get(x_0, 1);
lean::inc(x_321);
x_323 = lean::cnstr_get(x_0, 2);
lean::inc(x_323);
x_325 = 5;
x_326 = l_lean_ir_check__type(x_321, x_325, x_1, x_2);
lean::dec(x_2);
x_328 = lean::cnstr_get(x_326, 0);
lean::inc(x_328);
if (lean::obj_tag(x_328) == 0)
{
obj* x_332; obj* x_334; obj* x_335; obj* x_337; obj* x_338; obj* x_339; 
lean::dec(x_323);
lean::dec(x_1);
x_332 = lean::cnstr_get(x_326, 1);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 x_334 = x_326;
} else {
 lean::inc(x_332);
 lean::dec(x_326);
 x_334 = lean::box(0);
}
x_335 = lean::cnstr_get(x_328, 0);
if (lean::is_exclusive(x_328)) {
 x_337 = x_328;
} else {
 lean::inc(x_335);
 lean::dec(x_328);
 x_337 = lean::box(0);
}
if (lean::is_scalar(x_337)) {
 x_338 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_338 = x_337;
}
lean::cnstr_set(x_338, 0, x_335);
if (lean::is_scalar(x_334)) {
 x_339 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_339 = x_334;
}
lean::cnstr_set(x_339, 0, x_338);
lean::cnstr_set(x_339, 1, x_332);
x_3 = x_339;
goto lbl_4;
}
else
{
obj* x_341; obj* x_344; 
lean::dec(x_328);
x_341 = lean::cnstr_get(x_326, 1);
lean::inc(x_341);
lean::dec(x_326);
x_344 = l_lean_ir_check__type(x_323, x_325, x_1, x_341);
lean::dec(x_341);
lean::dec(x_1);
x_3 = x_344;
goto lbl_4;
}
}
case 14:
{
uint8 x_347; obj* x_348; obj* x_350; obj* x_352; obj* x_353; uint8 x_354; 
x_347 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_348 = lean::cnstr_get(x_0, 1);
lean::inc(x_348);
x_350 = lean::cnstr_get(x_0, 2);
lean::inc(x_350);
x_352 = l_lean_ir_type2id___main(x_347);
x_353 = l_lean_ir_valid__assign__unop__types___closed__1;
x_354 = lean::nat_dec_eq(x_352, x_353);
lean::dec(x_352);
if (x_354 == 0)
{
uint8 x_356; obj* x_357; obj* x_359; 
x_356 = 5;
x_357 = l_lean_ir_check__type(x_348, x_356, x_1, x_2);
lean::dec(x_2);
x_359 = lean::cnstr_get(x_357, 0);
lean::inc(x_359);
if (lean::obj_tag(x_359) == 0)
{
obj* x_363; obj* x_365; obj* x_366; obj* x_368; obj* x_369; obj* x_370; 
lean::dec(x_350);
lean::dec(x_1);
x_363 = lean::cnstr_get(x_357, 1);
if (lean::is_exclusive(x_357)) {
 lean::cnstr_release(x_357, 0);
 x_365 = x_357;
} else {
 lean::inc(x_363);
 lean::dec(x_357);
 x_365 = lean::box(0);
}
x_366 = lean::cnstr_get(x_359, 0);
if (lean::is_exclusive(x_359)) {
 x_368 = x_359;
} else {
 lean::inc(x_366);
 lean::dec(x_359);
 x_368 = lean::box(0);
}
if (lean::is_scalar(x_368)) {
 x_369 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_369 = x_368;
}
lean::cnstr_set(x_369, 0, x_366);
if (lean::is_scalar(x_365)) {
 x_370 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_370 = x_365;
}
lean::cnstr_set(x_370, 0, x_369);
lean::cnstr_set(x_370, 1, x_363);
x_3 = x_370;
goto lbl_4;
}
else
{
obj* x_372; obj* x_375; obj* x_378; 
lean::dec(x_359);
x_372 = lean::cnstr_get(x_357, 1);
lean::inc(x_372);
lean::dec(x_357);
x_375 = l_lean_ir_check__type(x_350, x_356, x_1, x_372);
lean::dec(x_372);
lean::dec(x_1);
x_378 = lean::cnstr_get(x_375, 0);
lean::inc(x_378);
if (lean::obj_tag(x_378) == 0)
{
obj* x_380; obj* x_382; obj* x_383; obj* x_385; obj* x_386; obj* x_387; 
x_380 = lean::cnstr_get(x_375, 1);
if (lean::is_exclusive(x_375)) {
 lean::cnstr_release(x_375, 0);
 x_382 = x_375;
} else {
 lean::inc(x_380);
 lean::dec(x_375);
 x_382 = lean::box(0);
}
x_383 = lean::cnstr_get(x_378, 0);
if (lean::is_exclusive(x_378)) {
 x_385 = x_378;
} else {
 lean::inc(x_383);
 lean::dec(x_378);
 x_385 = lean::box(0);
}
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_383);
if (lean::is_scalar(x_382)) {
 x_387 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_387 = x_382;
}
lean::cnstr_set(x_387, 0, x_386);
lean::cnstr_set(x_387, 1, x_380);
x_3 = x_387;
goto lbl_4;
}
else
{
obj* x_389; obj* x_391; obj* x_392; obj* x_393; 
lean::dec(x_378);
x_389 = lean::cnstr_get(x_375, 1);
if (lean::is_exclusive(x_375)) {
 lean::cnstr_release(x_375, 0);
 x_391 = x_375;
} else {
 lean::inc(x_389);
 lean::dec(x_375);
 x_391 = lean::box(0);
}
x_392 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_391)) {
 x_393 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_393 = x_391;
}
lean::cnstr_set(x_393, 0, x_392);
lean::cnstr_set(x_393, 1, x_389);
x_3 = x_393;
goto lbl_4;
}
}
}
else
{
uint8 x_394; obj* x_395; obj* x_397; 
x_394 = 5;
x_395 = l_lean_ir_check__type(x_348, x_394, x_1, x_2);
lean::dec(x_2);
x_397 = lean::cnstr_get(x_395, 0);
lean::inc(x_397);
if (lean::obj_tag(x_397) == 0)
{
obj* x_401; obj* x_403; obj* x_404; obj* x_406; obj* x_407; obj* x_408; 
lean::dec(x_350);
lean::dec(x_1);
x_401 = lean::cnstr_get(x_395, 1);
if (lean::is_exclusive(x_395)) {
 lean::cnstr_release(x_395, 0);
 x_403 = x_395;
} else {
 lean::inc(x_401);
 lean::dec(x_395);
 x_403 = lean::box(0);
}
x_404 = lean::cnstr_get(x_397, 0);
if (lean::is_exclusive(x_397)) {
 x_406 = x_397;
} else {
 lean::inc(x_404);
 lean::dec(x_397);
 x_406 = lean::box(0);
}
if (lean::is_scalar(x_406)) {
 x_407 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_407 = x_406;
}
lean::cnstr_set(x_407, 0, x_404);
if (lean::is_scalar(x_403)) {
 x_408 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_408 = x_403;
}
lean::cnstr_set(x_408, 0, x_407);
lean::cnstr_set(x_408, 1, x_401);
x_3 = x_408;
goto lbl_4;
}
else
{
obj* x_410; obj* x_413; obj* x_416; 
lean::dec(x_397);
x_410 = lean::cnstr_get(x_395, 1);
lean::inc(x_410);
lean::dec(x_395);
x_413 = l_lean_ir_check__type(x_350, x_394, x_1, x_410);
lean::dec(x_410);
lean::dec(x_1);
x_416 = lean::cnstr_get(x_413, 0);
lean::inc(x_416);
if (lean::obj_tag(x_416) == 0)
{
obj* x_418; obj* x_420; obj* x_421; obj* x_423; obj* x_424; obj* x_425; 
x_418 = lean::cnstr_get(x_413, 1);
if (lean::is_exclusive(x_413)) {
 lean::cnstr_release(x_413, 0);
 x_420 = x_413;
} else {
 lean::inc(x_418);
 lean::dec(x_413);
 x_420 = lean::box(0);
}
x_421 = lean::cnstr_get(x_416, 0);
if (lean::is_exclusive(x_416)) {
 x_423 = x_416;
} else {
 lean::inc(x_421);
 lean::dec(x_416);
 x_423 = lean::box(0);
}
if (lean::is_scalar(x_423)) {
 x_424 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_424 = x_423;
}
lean::cnstr_set(x_424, 0, x_421);
if (lean::is_scalar(x_420)) {
 x_425 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_425 = x_420;
}
lean::cnstr_set(x_425, 0, x_424);
lean::cnstr_set(x_425, 1, x_418);
x_3 = x_425;
goto lbl_4;
}
else
{
obj* x_427; obj* x_429; obj* x_430; obj* x_431; 
lean::dec(x_416);
x_427 = lean::cnstr_get(x_413, 1);
if (lean::is_exclusive(x_413)) {
 lean::cnstr_release(x_413, 0);
 x_429 = x_413;
} else {
 lean::inc(x_427);
 lean::dec(x_413);
 x_429 = lean::box(0);
}
x_430 = l_lean_ir_instr_check___closed__5;
if (lean::is_scalar(x_429)) {
 x_431 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_431 = x_429;
}
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_427);
x_3 = x_431;
goto lbl_4;
}
}
}
}
default:
{
obj* x_432; obj* x_434; uint8 x_436; obj* x_437; obj* x_439; 
x_432 = lean::cnstr_get(x_0, 0);
lean::inc(x_432);
x_434 = lean::cnstr_get(x_0, 1);
lean::inc(x_434);
x_436 = 11;
x_437 = l_lean_ir_check__type(x_432, x_436, x_1, x_2);
lean::dec(x_2);
x_439 = lean::cnstr_get(x_437, 0);
lean::inc(x_439);
if (lean::obj_tag(x_439) == 0)
{
obj* x_443; obj* x_445; obj* x_446; obj* x_448; obj* x_449; obj* x_450; 
lean::dec(x_1);
lean::dec(x_434);
x_443 = lean::cnstr_get(x_437, 1);
if (lean::is_exclusive(x_437)) {
 lean::cnstr_release(x_437, 0);
 x_445 = x_437;
} else {
 lean::inc(x_443);
 lean::dec(x_437);
 x_445 = lean::box(0);
}
x_446 = lean::cnstr_get(x_439, 0);
if (lean::is_exclusive(x_439)) {
 x_448 = x_439;
} else {
 lean::inc(x_446);
 lean::dec(x_439);
 x_448 = lean::box(0);
}
if (lean::is_scalar(x_448)) {
 x_449 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_449 = x_448;
}
lean::cnstr_set(x_449, 0, x_446);
if (lean::is_scalar(x_445)) {
 x_450 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_450 = x_445;
}
lean::cnstr_set(x_450, 0, x_449);
lean::cnstr_set(x_450, 1, x_443);
x_3 = x_450;
goto lbl_4;
}
else
{
obj* x_452; uint8 x_455; obj* x_456; 
lean::dec(x_439);
x_452 = lean::cnstr_get(x_437, 1);
lean::inc(x_452);
lean::dec(x_437);
x_455 = 5;
x_456 = l_lean_ir_check__type(x_434, x_455, x_1, x_452);
lean::dec(x_452);
lean::dec(x_1);
x_3 = x_456;
goto lbl_4;
}
}
}
lbl_4:
{
obj* x_459; 
x_459 = lean::cnstr_get(x_3, 0);
lean::inc(x_459);
if (lean::obj_tag(x_459) == 0)
{
obj* x_461; obj* x_463; obj* x_464; obj* x_466; obj* x_467; uint8 x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; 
x_461 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_463 = x_3;
} else {
 lean::inc(x_461);
 lean::dec(x_3);
 x_463 = lean::box(0);
}
x_464 = lean::cnstr_get(x_459, 0);
if (lean::is_exclusive(x_459)) {
 x_466 = x_459;
} else {
 lean::inc(x_464);
 lean::dec(x_459);
 x_466 = lean::box(0);
}
x_467 = l_lean_ir_instr_to__format___main(x_0);
x_468 = 0;
x_469 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_470 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_470, 0, x_469);
lean::cnstr_set(x_470, 1, x_467);
lean::cnstr_set_scalar(x_470, sizeof(void*)*2, x_468);
x_471 = x_470;
x_472 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_473 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_473, 0, x_471);
lean::cnstr_set(x_473, 1, x_472);
lean::cnstr_set_scalar(x_473, sizeof(void*)*2, x_468);
x_474 = x_473;
x_475 = lean::box(1);
x_476 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_475);
lean::cnstr_set_scalar(x_476, sizeof(void*)*2, x_468);
x_477 = x_476;
x_478 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_478, 0, x_477);
lean::cnstr_set(x_478, 1, x_464);
lean::cnstr_set_scalar(x_478, sizeof(void*)*2, x_468);
x_479 = x_478;
if (lean::is_scalar(x_466)) {
 x_480 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_480 = x_466;
}
lean::cnstr_set(x_480, 0, x_479);
if (lean::is_scalar(x_463)) {
 x_481 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_481 = x_463;
}
lean::cnstr_set(x_481, 0, x_480);
lean::cnstr_set(x_481, 1, x_461);
return x_481;
}
else
{
obj* x_483; obj* x_485; obj* x_486; 
lean::dec(x_0);
x_483 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_485 = x_3;
} else {
 lean::inc(x_483);
 lean::dec(x_3);
 x_485 = lean::box(0);
}
if (lean::is_scalar(x_485)) {
 x_486 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_486 = x_485;
}
lean::cnstr_set(x_486, 0, x_459);
lean::cnstr_set(x_486, 1, x_483);
return x_486;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_8; uint8 x_11; obj* x_12; obj* x_14; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_12 = l_lean_ir_check__type(x_6, x_11, x_2, x_3);
lean::dec(x_3);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_22 = x_14;
} else {
 lean::inc(x_20);
 lean::dec(x_14);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_14);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_1 = x_8;
x_3 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_phi_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1(x_0, x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_13 = x_6;
} else {
 lean::inc(x_11);
 lean::dec(x_6);
 x_13 = lean::box(0);
}
x_14 = l_lean_ir_phi_to__format___main(x_0);
x_15 = 0;
x_16 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_15);
x_18 = x_17;
x_19 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_15);
x_21 = x_20;
x_22 = lean::box(1);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_15);
x_24 = x_23;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_11);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_15);
x_26 = x_25;
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_26);
if (lean::is_scalar(x_10)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_10;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_8);
return x_28;
}
else
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_0);
x_30 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_32 = x_5;
} else {
 lean::inc(x_30);
 lean::dec(x_5);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_6);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_ir_phi_check___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_phi_check(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_check__result__type___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_check__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_check__result__type___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_check__result__type___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_ir_check__result__type(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_check__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_check__result__type___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_check__result__type(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* _init_l_lean_ir_terminator_check___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("variable must be an uint32 or bool");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_ir_terminator_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::unbox(x_8);
x_10 = l_lean_ir_check__type(x_6, x_9, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_3 = x_11;
x_4 = x_13;
goto lbl_5;
}
case 1:
{
obj* x_16; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = l_lean_ir_get__type(x_16, x_1, x_2);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_26 = x_19;
} else {
 lean::inc(x_24);
 lean::dec(x_19);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
x_3 = x_27;
x_4 = x_21;
goto lbl_5;
}
else
{
obj* x_28; obj* x_31; uint8 x_34; obj* x_35; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_18, 1);
lean::inc(x_28);
lean::dec(x_18);
x_31 = lean::cnstr_get(x_19, 0);
lean::inc(x_31);
lean::dec(x_19);
x_34 = lean::unbox(x_31);
x_35 = l_lean_ir_type2id___main(x_34);
x_36 = l_lean_ir_is__arith__ty___closed__1;
x_37 = lean::nat_dec_eq(x_35, x_36);
if (x_37 == 0)
{
obj* x_38; uint8 x_39; 
x_38 = l_lean_ir_valid__assign__unop__types___closed__3;
x_39 = lean::nat_dec_eq(x_35, x_38);
lean::dec(x_35);
if (x_39 == 0)
{
obj* x_41; 
x_41 = l_lean_ir_terminator_check___closed__1;
x_3 = x_41;
x_4 = x_28;
goto lbl_5;
}
else
{
obj* x_42; 
x_42 = l_lean_ir_match__type___closed__5;
x_3 = x_42;
x_4 = x_28;
goto lbl_5;
}
}
else
{
obj* x_44; 
lean::dec(x_35);
x_44 = l_lean_ir_match__type___closed__5;
x_3 = x_44;
x_4 = x_28;
goto lbl_5;
}
}
}
default:
{
obj* x_45; 
x_45 = l_lean_ir_match__type___closed__5;
lean::inc(x_2);
x_3 = x_45;
x_4 = x_2;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_47; obj* x_49; obj* x_50; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_47 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_49 = x_3;
} else {
 lean::inc(x_47);
 lean::dec(x_3);
 x_49 = lean::box(0);
}
x_50 = l_lean_ir_terminator_to__format___main(x_0);
x_51 = 0;
x_52 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
x_53 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_50);
lean::cnstr_set_scalar(x_53, sizeof(void*)*2, x_51);
x_54 = x_53;
x_55 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_51);
x_57 = x_56;
x_58 = lean::box(1);
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_58);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_51);
x_60 = x_59;
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_47);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_51);
x_62 = x_61;
if (lean::is_scalar(x_49)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_49;
}
lean::cnstr_set(x_63, 0, x_62);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_4);
return x_64;
}
else
{
obj* x_66; 
lean::dec(x_0);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_3);
lean::cnstr_set(x_66, 1, x_4);
return x_66;
}
}
}
}
obj* l_lean_ir_terminator_check___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_terminator_check(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_match__type___closed__5;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_phi_check(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_23;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_instr_check(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_block_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 3);
lean::inc(x_5);
x_10 = l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(x_3, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_18 = x_11;
} else {
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
x_7 = x_19;
x_8 = x_13;
goto lbl_9;
}
else
{
obj* x_21; obj* x_24; obj* x_27; obj* x_28; obj* x_30; 
lean::dec(x_11);
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
lean::dec(x_10);
x_24 = lean::cnstr_get(x_0, 2);
lean::inc(x_24);
lean::inc(x_1);
x_27 = l_list_mmap_x_27___main___at_lean_ir_block_check___spec__2(x_24, x_1, x_21);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
x_7 = x_28;
x_8 = x_30;
goto lbl_9;
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_35; obj* x_37; obj* x_38; obj* x_41; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_5);
lean::dec(x_1);
x_35 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_37 = x_7;
} else {
 lean::inc(x_35);
 lean::dec(x_7);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
x_41 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_38);
x_42 = 0;
x_43 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_44 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_41);
lean::cnstr_set_scalar(x_44, sizeof(void*)*2, x_42);
x_45 = x_44;
x_46 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_47 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_42);
x_48 = x_47;
x_49 = lean::box(1);
x_50 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set_scalar(x_50, sizeof(void*)*2, x_42);
x_51 = x_50;
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_35);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_42);
x_53 = x_52;
if (lean::is_scalar(x_37)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_37;
}
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_8);
return x_55;
}
else
{
obj* x_57; obj* x_60; 
lean::dec(x_7);
x_57 = l_lean_ir_terminator_check(x_5, x_1, x_8);
lean::dec(x_8);
lean::dec(x_1);
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
if (lean::obj_tag(x_60) == 0)
{
obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_71; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_62 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_64 = x_57;
} else {
 lean::inc(x_62);
 lean::dec(x_57);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_67 = x_60;
} else {
 lean::inc(x_65);
 lean::dec(x_60);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_0, 0);
lean::inc(x_68);
lean::dec(x_0);
x_71 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_68);
x_72 = 0;
x_73 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_71);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_72);
x_75 = x_74;
x_76 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_77 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set(x_77, 1, x_76);
lean::cnstr_set_scalar(x_77, sizeof(void*)*2, x_72);
x_78 = x_77;
x_79 = lean::box(1);
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_72);
x_81 = x_80;
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_65);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_72);
x_83 = x_82;
if (lean::is_scalar(x_67)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_67;
}
lean::cnstr_set(x_84, 0, x_83);
if (lean::is_scalar(x_64)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_64;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_62);
return x_85;
}
else
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_0);
x_87 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_89 = x_57;
} else {
 lean::inc(x_87);
 lean::dec(x_57);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_60);
lean::cnstr_set(x_90, 1, x_87);
return x_90;
}
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_block_check(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_decl_check___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_list_mmap_x_27___main___at_lean_ir_decl_check___main___spec__1(x_7, x_1, x_2);
return x_10;
}
}
}
obj* l_lean_ir_decl_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_decl_check___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
if (lean::is_scalar(x_8)) {
 x_9 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_9 = x_8;
}
lean::cnstr_set(x_9, 0, x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
else
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::apply_3(x_0, x_11, x_2, x_3);
return x_14;
}
}
}
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_11; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_3(x_1, x_6, x_2, x_8);
return x_11;
}
}
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_ir_type__check___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_decl_check___main(x_0, x_2, x_3);
return x_4;
}
}
obj* l_lean_ir_type__check___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; 
lean::inc(x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
}
obj* _init_l_lean_ir_type__check___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_type__check___lambda__2___boxed), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg), 4, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_type__check(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_15; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_decl_infer__types), 3, 1);
lean::closure_set(x_3, 0, x_0);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_type__check___lambda__1___boxed), 4, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg), 4, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg), 4, 2);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, x_6);
x_8 = l_lean_ir_type__check___closed__1;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg), 4, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = l_lean_ir_decl_header___main(x_0);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_10, 2);
lean::inc(x_12);
lean::dec(x_10);
x_15 = l_lean_ir_type__checker__m_run___rarg(x_9, x_1, x_12);
lean::dec(x_12);
return x_15;
}
}
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_except__t_bind__cont___at_lean_ir_type__check___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_reader__t_bind___at_lean_ir_type__check___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_ir_type__check___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_type__check___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_ir_type__check___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_type__check___lambda__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_type__check___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_type__check(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
void initialize_init_lean_ir_instances();
void initialize_init_lean_ir_format();
void initialize_init_control_combinators();
static bool _G_initialized = false;
void initialize_init_lean_ir_type__check() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_ir_instances();
 initialize_init_lean_ir_format();
 initialize_init_control_combinators();
 l_lean_ir_is__arith__ty___closed__1 = _init_l_lean_ir_is__arith__ty___closed__1();
lean::mark_persistent(l_lean_ir_is__arith__ty___closed__1);
 l_lean_ir_is__nonfloat__arith__ty___closed__1 = _init_l_lean_ir_is__nonfloat__arith__ty___closed__1();
lean::mark_persistent(l_lean_ir_is__nonfloat__arith__ty___closed__1);
 l_lean_ir_is__nonfloat__arith__ty___closed__2 = _init_l_lean_ir_is__nonfloat__arith__ty___closed__2();
lean::mark_persistent(l_lean_ir_is__nonfloat__arith__ty___closed__2);
 l_lean_ir_valid__assign__unop__types___closed__1 = _init_l_lean_ir_valid__assign__unop__types___closed__1();
lean::mark_persistent(l_lean_ir_valid__assign__unop__types___closed__1);
 l_lean_ir_valid__assign__unop__types___closed__2 = _init_l_lean_ir_valid__assign__unop__types___closed__2();
lean::mark_persistent(l_lean_ir_valid__assign__unop__types___closed__2);
 l_lean_ir_valid__assign__unop__types___closed__3 = _init_l_lean_ir_valid__assign__unop__types___closed__3();
lean::mark_persistent(l_lean_ir_valid__assign__unop__types___closed__3);
 l_lean_ir_valid__assign__unop__types___closed__4 = _init_l_lean_ir_valid__assign__unop__types___closed__4();
lean::mark_persistent(l_lean_ir_valid__assign__unop__types___closed__4);
 l_lean_ir_type__checker__m = _init_l_lean_ir_type__checker__m();
lean::mark_persistent(l_lean_ir_type__checker__m);
 l_lean_ir_match__type___closed__1 = _init_l_lean_ir_match__type___closed__1();
lean::mark_persistent(l_lean_ir_match__type___closed__1);
 l_lean_ir_match__type___closed__2 = _init_l_lean_ir_match__type___closed__2();
lean::mark_persistent(l_lean_ir_match__type___closed__2);
 l_lean_ir_match__type___closed__3 = _init_l_lean_ir_match__type___closed__3();
lean::mark_persistent(l_lean_ir_match__type___closed__3);
 l_lean_ir_match__type___closed__4 = _init_l_lean_ir_match__type___closed__4();
lean::mark_persistent(l_lean_ir_match__type___closed__4);
 l_lean_ir_match__type___closed__5 = _init_l_lean_ir_match__type___closed__5();
lean::mark_persistent(l_lean_ir_match__type___closed__5);
 l_lean_ir_get__type___closed__1 = _init_l_lean_ir_get__type___closed__1();
lean::mark_persistent(l_lean_ir_get__type___closed__1);
 l_lean_ir_check__type___closed__1 = _init_l_lean_ir_check__type___closed__1();
lean::mark_persistent(l_lean_ir_check__type___closed__1);
 l_lean_ir_check__type___closed__2 = _init_l_lean_ir_check__type___closed__2();
lean::mark_persistent(l_lean_ir_check__type___closed__2);
 l_lean_ir_check__ne__type___closed__1 = _init_l_lean_ir_check__ne__type___closed__1();
lean::mark_persistent(l_lean_ir_check__ne__type___closed__1);
 l_lean_ir_check__ne__type___closed__2 = _init_l_lean_ir_check__ne__type___closed__2();
lean::mark_persistent(l_lean_ir_check__ne__type___closed__2);
 l_lean_ir_invalid__literal___rarg___closed__1 = _init_l_lean_ir_invalid__literal___rarg___closed__1();
lean::mark_persistent(l_lean_ir_invalid__literal___rarg___closed__1);
 l_lean_ir_get__decl___closed__1 = _init_l_lean_ir_get__decl___closed__1();
lean::mark_persistent(l_lean_ir_get__decl___closed__1);
 l_lean_ir_check__arg__types___main___closed__1 = _init_l_lean_ir_check__arg__types___main___closed__1();
lean::mark_persistent(l_lean_ir_check__arg__types___main___closed__1);
 l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1 = _init_l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1);
 l_lean_ir_instr_check___closed__1 = _init_l_lean_ir_instr_check___closed__1();
lean::mark_persistent(l_lean_ir_instr_check___closed__1);
 l_lean_ir_instr_check___closed__2 = _init_l_lean_ir_instr_check___closed__2();
lean::mark_persistent(l_lean_ir_instr_check___closed__2);
 l_lean_ir_instr_check___closed__3 = _init_l_lean_ir_instr_check___closed__3();
lean::mark_persistent(l_lean_ir_instr_check___closed__3);
 l_lean_ir_instr_check___closed__4 = _init_l_lean_ir_instr_check___closed__4();
lean::mark_persistent(l_lean_ir_instr_check___closed__4);
 l_lean_ir_instr_check___closed__5 = _init_l_lean_ir_instr_check___closed__5();
lean::mark_persistent(l_lean_ir_instr_check___closed__5);
 l_lean_ir_terminator_check___closed__1 = _init_l_lean_ir_terminator_check___closed__1();
lean::mark_persistent(l_lean_ir_terminator_check___closed__1);
 l_lean_ir_type__check___closed__1 = _init_l_lean_ir_type__check___closed__1();
lean::mark_persistent(l_lean_ir_type__check___closed__1);
}
