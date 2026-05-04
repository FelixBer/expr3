// Standalone test suite for expr3.h
// Build: g++ -std=c++17 -Wall -o test test.cpp && ./test
//        cl /std:c++17 /W4 /EHsc test.cpp /Fetest.exe

#include "expr3.h"

#include <cmath>
#include <iomanip>
#include <iostream>
#include <map>
#include <string>

using namespace expr3;

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

static int g_pass = 0, g_fail = 0;

// Boolean condition (ok flags, is_error(), etc.)
static void check(bool ok, const char* name)
{
    if (ok) { ++g_pass; return; }
    ++g_fail;
    std::cout << "  [FAIL] " << name << "\n"
              << "         expected: true\n"
              << "         actual:   false\n";
}

// Generic value equality — prints expected/actual on failure
template<typename T>
static void check_eq(T actual, T expected, const char* name)
{
    if (actual == expected) { ++g_pass; return; }
    ++g_fail;
    std::cout << "  [FAIL] " << name << "\n"
              << "         expected: " << expected << "\n"
              << "         actual:   " << actual   << "\n";
}

// uint64_t — show in hex
template<>
void check_eq<uint64_t>(uint64_t actual, uint64_t expected, const char* name)
{
    if (actual == expected) { ++g_pass; return; }
    ++g_fail;
    std::cout << "  [FAIL] " << name << "\n"
              << std::hex << std::showbase
              << "         expected: " << expected << "\n"
              << "         actual:   " << actual   << "\n"
              << std::dec << std::noshowbase;
}

// Floating-point near-equality
static bool near(double a, double b) { return std::abs(a - b) < 1e-9; }

static void check_near(double actual, double expected, const char* name)
{
    if (near(actual, expected)) { ++g_pass; return; }
    ++g_fail;
    std::cout << "  [FAIL] " << name << "\n"
              << std::setprecision(15)
              << "         expected: ~" << expected << "\n"
              << "         actual:   "  << actual   << "\n";
}

// ---------------------------------------------------------------------------
// Variable/assignment context
// ---------------------------------------------------------------------------

class MapContext : public expr_eval_context
{
public:
    std::map<std::string, uint64_t> vars;

    Token resolve_var_if_needed(const Token& t) override
    {
        if (t.type == Token::Type::Number && !t.is_integer() && !t.is_double()) {
            auto it = vars.find(t.str);
            if (it != vars.end())
                return Token::make_constant(it->second);
        }
        return t;
    }
    bool assign(const Token& dest, const Token& val) override
    {
        if (dest.type == Token::Type::Number && !dest.is_integer() && !dest.is_double())
            vars[dest.str] = val.as_integer();
        return true;
    }
    Token exec_function(const Token&, std::vector<Token>&) override { return {}; }
};

// Convenience eval helpers
static uint64_t eu(const char* s, bool* ok = nullptr) { expr3u e(s); return e.eval(ok); }
static int64_t  es(const char* s, bool* ok = nullptr) { expr3s e(s); return e.eval(ok); }
static double   ef(const char* s, bool* ok = nullptr) { expr3f e(s); return e.eval(ok); }

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

static void test_arithmetic()
{
    std::cout << "\n=== Basic Arithmetic ===\n";
    check_eq(eu("1+2"),     3ULL,  "1+2");
    check_eq(eu("10-3"),    13ULL, "10-3");   // 0x10-3 = 16-3 = 13
    check_eq(eu("3*4"),     12ULL, "3*4");
    check_eq(eu("8/2"),     4ULL,  "8/2");
    check_eq(eu("7%3"),     1ULL,  "7%3");
    check_eq(eu("2+3*4"),   14ULL, "2+3*4 (precedence)");
    check_eq(eu("(2+3)*4"), 20ULL, "(2+3)*4");
    check_eq(eu("10-3-2"),  11ULL, "10-3-2 (left-assoc)"); // 0x10-3-2 = 11
    check_eq(eu("2*3+4*5"), 26ULL, "2*3+4*5");
}

static void test_bitwise()
{
    std::cout << "\n=== Bitwise Operators ===\n";
    check_eq(eu("0xF0&0x0F"), 0x00ULL,                  "0xF0 & 0x0F");
    check_eq(eu("0xF0|0x0F"), 0xFFULL,                  "0xF0 | 0x0F");
    check_eq(eu("0xFF^0x0F"), 0xF0ULL,                  "0xFF ^ 0x0F");
    check_eq(eu("~0"),        0xFFFFFFFFFFFFFFFFULL,     "~0");
    check_eq(eu("~0xFF"),     0xFFFFFFFFFFFFFF00ULL,     "~0xFF");
    check_eq(eu("1|2&3"),     3ULL,                      "1|2&3 (& before |)");
    check_eq(eu("~0&0xFF"),   0xFFULL,                   "~0&0xFF (~ before &)");
}

static void test_shifts_and_rotates()
{
    std::cout << "\n=== Shifts and Rotates ===\n";
    check_eq(eu("1<<4"),            16ULL,                   "1<<4");
    check_eq(eu("16>>2"),           5ULL,                    "16>>2"); // 0x16>>2 = 22>>2 = 5
    check_eq(eu("0xFF<<8>>4"),      0xFF0ULL,                "0xFF<<8>>4");
    check_eq(eu("0x8000000000000000<<<1"), 1ULL,             "0x8000000000000000<<<1 (ROL)");
    check_eq(eu("1>>>1"),           0x8000000000000000ULL,   "1>>>1 (ROR)");
}

static void test_unary_integer()
{
    std::cout << "\n=== Unary Operators (integer) ===\n";
    check_eq(eu("!0"),    1ULL, "!0");
    check_eq(eu("!1"),    0ULL, "!1");
    check_eq(eu("!5"),    0ULL, "!5");
    check_eq(eu("!!1"),   1ULL, "!!1");
    check_eq(es("-5"),    -5LL, "-5");
    check_eq(es("-(3)"),  -3LL, "-(3)");
    check_eq(es("-(-3)"),  3LL, "-(-3)");
}

// BUG #2 (fixed): float ~ was using li instead of ri
// BUG #3 (fixed): float ! was using li instead of ri
static void test_unary_float()
{
    std::cout << "\n=== Float Unary Ops ===\n";
    check_near(ef("!1.0"), 0.0, "float !1.0");
    check_near(ef("!5.0"), 0.0, "float !5.0");
    check_near(ef("!0.0"), 1.0, "float !0.0");

}

// BUG #1 (fixed): && and || were never produced by the tokenizer
static void test_logical()
{
    std::cout << "\n=== Logical && / || ===\n";
    check_eq(eu("1&&1"),   1ULL, "1&&1");
    check_eq(eu("2&&1"),   1ULL, "2&&1");
    check_eq(eu("1&&0"),   0ULL, "1&&0");
    check_eq(eu("0&&1"),   0ULL, "0&&1");
    check_eq(eu("0&&0"),   0ULL, "0&&0");
    check_eq(eu("1&&1&&1"),1ULL, "1&&1&&1");
    check_eq(eu("0||0"),   0ULL, "0||0");
    check_eq(eu("0||1"),   1ULL, "0||1");
    check_eq(eu("1||0"),   1ULL, "1||0");
    check_eq(eu("2||3"),   1ULL, "2||3");
}

static void test_comparisons()
{
    std::cout << "\n=== Comparison Operators ===\n";
    check_eq(eu("3==3"),   1ULL, "3==3");
    check_eq(eu("3==4"),   0ULL, "3==4");
    check_eq(eu("3!=4"),   1ULL, "3!=4");
    check_eq(eu("3!=3"),   0ULL, "3!=3");
    check_eq(eu("3<4"),    1ULL, "3<4");
    check_eq(eu("4<3"),    0ULL, "4<3");
    check_eq(eu("3<=3"),   1ULL, "3<=3");
    check_eq(eu("3<=4"),   1ULL, "3<=4");
    check_eq(eu("4<=3"),   0ULL, "4<=3");
    check_eq(eu("4>3"),    1ULL, "4>3");
    check_eq(eu("3>4"),    0ULL, "3>4");
    check_eq(eu("4>=4"),   1ULL, "4>=4");
    check_eq(eu("4>=3"),   1ULL, "4>=3");
    check_eq(eu("3>=4"),   0ULL, "3>=4");
    check_eq(eu("1+2==3"), 1ULL, "1+2==3");
    check_eq(eu("1+1==3"), 0ULL, "1+1==3");
}

static void test_float_arithmetic()
{
    std::cout << "\n=== Float Arithmetic ===\n";
    check_near(ef("1.5+2.5"),       4.0, "1.5+2.5");
    check_near(ef("3.0*2.5"),       7.5, "3.0*2.5");
    check_near(ef("7.5/2.5"),       3.0, "7.5/2.5");
    check_near(ef("2.5-1.0"),       1.5, "2.5-1.0");
    check_near(ef("7.5%2.5"),       0.0, "7.5%2.5 (fmod)");
    check_near(ef("5.0%3.0"),       2.0, "5.0%3.0 (fmod)");
    check_near(ef("(1.5+2.5)*2.0"), 8.0, "(1.5+2.5)*2.0");
}

static void test_functions()
{
    std::cout << "\n=== Built-in Functions ===\n";
    check_eq(eu("max(3,5)"),        5ULL, "max(3,5)");
    check_eq(eu("max(5,3)"),        5ULL, "max(5,3)");
    check_eq(eu("min(3,5)"),        3ULL, "min(3,5)");
    check_eq(eu("min(5,3)"),        3ULL, "min(5,3)");
    check_near(ef("max(1.5,2.5)"), 2.5,  "max(1.5,2.5)");
    check_near(ef("min(1.5,2.5)"), 1.5,  "min(1.5,2.5)");
    check_eq(eu("max(max(1,3),2)"), 3ULL, "max(max(1,3),2)");
}

static void test_variables()
{
    std::cout << "\n=== Variables via Context ===\n";
    MapContext ctx;
    ctx.vars["x"] = 42;
    ctx.vars["z"] = 8;

    expr3u e;
    bool ok;

    e.set_from_string("x+z");
    check_eq(e.eval(&ok, &ctx), 50ULL,  "x+z (x=42, z=8)");
    check(ok, "x+z ok");

    e.set_from_string("x*z");
    check_eq(e.eval(&ok, &ctx), 336ULL, "x*z");

    e.set_from_string("x-z");
    check_eq(e.eval(&ok, &ctx), 34ULL,  "x-z");

    expr3f ef2("pi");
    double pi_val = ef2.eval(&ok);
    check(ok, "pi ok");
    check_near(pi_val, 3.141593, "pi value"); // double_as_str uses std::fixed precision 6
}

static void test_assignment_ops()
{
    std::cout << "\n=== Assignment Operators ===\n";
    MapContext ctx;
    expr3u e;
    bool ok;

#define ASSIGN_TEST(init, expr_str, expected, label) \
    ctx.vars["x"] = (init); \
    e.set_from_string(expr_str); \
    e.eval(&ok, &ctx); \
    check(ok, label " ok"); \
    check_eq(ctx.vars["x"], (uint64_t)(expected), label)

    ASSIGN_TEST(10,   "x+=5",    15,    "x+=5");
    ASSIGN_TEST(10,   "x-=3",    7,     "x-=3");
    ASSIGN_TEST(10,   "x*=2",    20,    "x*=2");
    ASSIGN_TEST(10,   "x/=2",    5,     "x/=2");
    ASSIGN_TEST(0xF0, "x&=0x0F", 0,     "x&=0x0F");
    ASSIGN_TEST(0xF0, "x|=0x0F", 0xFF,  "x|=0x0F");
    ASSIGN_TEST(0xFF, "x^=0x0F", 0xF0,  "x^=0x0F");
    ASSIGN_TEST(1,    "x<<=3",   8,     "x<<=3");
    ASSIGN_TEST(0x10, "x>>=2",   4,     "x>>=2");

#undef ASSIGN_TEST
}

static void test_signed_arithmetic()
{
    std::cout << "\n=== Signed Integer (expr3s) ===\n";
    check_eq(es("-5+3"),    -2LL,  "-5+3");
    check_eq(es("10-20"),  -16LL,  "10-20");  // 0x10-0x20 = 16-32 = -16
    check_eq(es("-3*4"),   -12LL,  "-3*4");
    check_eq(es("-10/-2"),   8LL,  "-10/-2"); // -0x10/-0x2 = -16/-2 = 8
    check_eq(es("1<<3"),     8LL,  "1<<3");
    check_eq(es("--5"),      5LL,  "--5");
}

// BUG #4 (fixed): str_as_double always set ok=true
static void test_str_as_double()
{
    std::cout << "\n=== str_as_double correctness ===\n";
    Token t_bad(Token::Type::Number, "abc.def");
    check_eq(t_bad.is_double(), false, "is_double(\"abc.def\")");

    Token t_no_dot(Token::Type::Number, "xyz");
    check_eq(t_no_dot.is_double(), false, "is_double(\"xyz\")");

    Token t_ok(Token::Type::Number, "3.14");
    double v = 0.0;
    check_eq(t_ok.is_double(&v), true, "is_double(\"3.14\")");
    check_near(v, 3.14, "is_double(\"3.14\") value");
}

// BUG #5: no div-by-zero guard — float is safely testable
static void test_division_by_zero()
{
    std::cout << "\n=== Division by Zero ===\n";
    check(std::isinf(ef("1.0/0.0")), "1.0/0.0 == inf");
    check(std::isnan(ef("5.0%0.0")), "5.0%0.0 == nan (fmod)");
    bool ok;
    eu("1/0", &ok);
    check(!ok, "integer 1/0 returns error");
    eu("5%0", &ok);
    check(!ok, "integer 5%0 returns error");
}

// BUG #8 (fixed): set_from_string returned Token(data.empty())
static void test_set_from_string_return()
{
    std::cout << "\n=== set_from_string return value ===\n";
    expr3u e;

    Token r_ok = e.set_from_string("1+2");
    check(!r_ok.is_error(),   "set_from_string(\"1+2\") not error");
    check(!r_ok.is_number(),  "set_from_string success not a Number token");

    Token r_err = e.set_from_string("((1+2)");
    check(r_err.is_error(), "set_from_string(\"((1+2)\") is error");

    Token r_empty = e.set_from_string("");
    check(r_empty.is_error(), "set_from_string(\"\") is error");
}

// BUG #9: is_integer tries base-16 twice; also documents default_base=16
static void test_is_integer_base()
{
    std::cout << "\n=== is_integer base fallback ===\n";
    Token t1(Token::Type::Number, "10");
    uint64_t v1 = 0;
    check(t1.is_integer(&v1), "is_integer(\"10\") true");
    check_eq(v1, 16ULL,       "is_integer(\"10\") == 16 (default_base=16)");

    Token t2(Token::Type::Number, "FF");
    uint64_t v2 = 0;
    check(t2.is_integer(&v2), "is_integer(\"FF\") true");
    check_eq(v2, 255ULL,      "is_integer(\"FF\") == 255");

    Token t3(Token::Type::Number, "99");
    uint64_t v3 = 0;
    t3.is_integer(&v3);
    check_eq(v3, 0x99ULL, "is_integer(\"99\") == 0x99 (hex wins)");

    Token t4(Token::Type::Number, "GG");
    check_eq(t4.is_integer(), false, "is_integer(\"GG\") false");
}

static void test_error_handling()
{
    std::cout << "\n=== Error Handling ===\n";
    expr3u e;
    bool ok;

    check(e.set_from_string("(1+2").is_error(),  "\"(1+2\" parse error");
    check(e.set_from_string("1+2)").is_error(),  "\"1+2)\" parse error");

    e.set_from_string("1+");
    e.eval(&ok);
    check(!ok, "\"1+\" eval fails");
}

static void test_intermediate_repr()
{
    std::cout << "\n=== Intermediate (RPN) Representation ===\n";
    expr3u e;

    e.set_from_string("1+2*3");
    check_eq(e.intermediate_repr(), std::string("1 2 3 * + "), "\"1+2*3\" RPN");

    e.set_from_string("(1+2)*3");
    check_eq(e.intermediate_repr(), std::string("1 2 + 3 * "), "\"(1+2)*3\" RPN");
}

static void test_unary_chain()
{
    std::cout << "\n=== Unary Operator Chains ===\n";
    check_eq(es("---5"),  -5LL,  "---5 == -5");
    check_eq(es("----5"),  5LL,  "----5 == 5");
    check_eq(eu("!!!1"),   0ULL, "!!!1 == 0");
    check_eq(eu("!!!0"),   1ULL, "!!!0 == 1");
}

static void test_nested_functions()
{
    std::cout << "\n=== Nested Functions ===\n";
    check_eq(eu("min(max(1,3),2)"), 2ULL, "min(max(1,3),2)");
    check_eq(eu("max(min(1,3),2)"), 2ULL, "max(min(1,3),2)");
    check_eq(eu("min(max(2,5),max(1,3))"), 3ULL, "min(max(2,5),max(1,3))");
}

static void test_rotate_assign()
{
    std::cout << "\n=== Rotate-Assign Operators ===\n";
    MapContext ctx;
    expr3u e;
    bool ok;

    ctx.vars["x"] = 1;
    e.set_from_string("x<<<=3");
    e.eval(&ok, &ctx);
    check(ok, "x<<<=3 ok");
    check_eq(ctx.vars["x"], 8ULL, "x=1; x<<<=3 == 8");

    ctx.vars["x"] = 1;
    e.set_from_string("x>>>=1");
    e.eval(&ok, &ctx);
    check(ok, "x>>>=1 ok");
    check_eq(ctx.vars["x"], 0x8000000000000000ULL, "x=1; x>>>=1 == MSB");
}

static void test_assign_div_by_zero()
{
    std::cout << "\n=== Assign Op Division by Zero ===\n";
    MapContext ctx;
    expr3u e;
    bool ok;

    ctx.vars["x"] = 10;
    e.set_from_string("x/=0");
    e.eval(&ok, &ctx);
    check(!ok, "integer x/=0 returns error");

    ctx.vars["x"] = 10;
    e.set_from_string("x%=0");
    e.eval(&ok, &ctx);
    check(!ok, "integer x%=0 returns error");
}

// BUG: max/min return Token(false)==Token(0) (valid Number!) instead of an error
static void test_function_wrong_arity()
{
    std::cout << "\n=== Function Wrong Arity (Bug: silently returns 0) ===\n";
    bool ok;
    eu("max(1)", &ok);
    check(!ok, "max(1) returns error");
    eu("min(1)", &ok);
    check(!ok, "min(1) returns error");
    eu("max()", &ok);
    check(!ok, "max() returns error");
}

// BUG: float %=3.1 casts both operands to uint64_t and uses integer %, not fmod
static void test_float_assign_remainder()
{
    std::cout << "\n=== Float Assign Remainder (Bug: int% instead of fmod) ===\n";

    class FloatMapCtx : public expr_eval_context {
    public:
        std::map<std::string, double> vars;
        Token resolve_var_if_needed(const Token& t) override {
            if (t.type == Token::Type::Number && !t.is_integer() && !t.is_double()) {
                auto it = vars.find(t.str);
                if (it != vars.end())
                    return Token(it->second);
            }
            return t;
        }
        bool assign(const Token& dest, const Token& val) override {
            if (dest.type == Token::Type::Number && !dest.is_integer() && !dest.is_double())
                vars[dest.str] = val.as_double();
            return true;
        }
        Token exec_function(const Token&, std::vector<Token>&) override { return {}; }
    } ctx;

    ctx.vars["x"] = 5.3;
    expr3f e("x%=3.1");
    bool ok;
    e.eval(&ok, &ctx);
    check(ok, "float x%=3.1 ok");
    check_near(ctx.vars["x"], std::fmod(5.3, 3.1), "float x%=3.1 uses fmod");
}

// BUG: <= and >= are right-associative in create_from_type, but < and > are left-associative
static void test_comparison_associativity()
{
    std::cout << "\n=== Comparison Associativity (Bug: <= and >= are right-assoc) ===\n";
    // C++: 3<=4<=5 is (3<=4)<=5 = 1<=5 = 1
    check_eq(eu("3<=4<=5"), 1ULL, "3<=4<=5 == 1 (left-assoc)");
    // C++: 5>=4>=3 is (5>=4)>=3 = 1>=3 = 0
    check_eq(eu("5>=4>=3"), 0ULL, "5>=4>=3 == 0 (left-assoc)");
}

// ---------------------------------------------------------------------------

int main()
{
    std::cout << "expr3 Test Suite\n================";

    test_arithmetic();
    test_bitwise();
    test_shifts_and_rotates();
    test_unary_integer();
    test_unary_chain();
    test_unary_float();
    test_logical();
    test_comparisons();
    test_comparison_associativity();
    test_float_arithmetic();
    test_float_assign_remainder();
    test_functions();
    test_nested_functions();
    test_function_wrong_arity();
    test_variables();
    test_assignment_ops();
    test_rotate_assign();
    test_signed_arithmetic();
    test_str_as_double();
    test_division_by_zero();
    test_assign_div_by_zero();
    test_set_from_string_return();
    test_is_integer_base();
    test_error_handling();
    test_intermediate_repr();

    std::cout << "\n================\nResults:\n"
              << "  pass: " << g_pass << "\n"
              << "  fail: " << g_fail << "\n";

    return (g_fail > 0) ? 1 : 0;
}
