# expr3: Simple Expression Evaluation


Note: Tests, Examples and License will be added shortly.


expr3 is a header-only single-header C++11 library for evaluating number expressions.
It is based on the [Shunting Yard Algorithm](https://en.wikipedia.org/wiki/Shunting-yard_algorithm).


expr3 is templated with the number type the expression operates on.
For convenience, the common types of expressions are predefined:

    using expr3s = expr3<int64_t>;
    using expr3u = expr3<uint64_t>;
    using expr3f = expr3<double>;

Thus evaluating a basic uint64_t expression can be done like so:

    expr3::expr3u ex("1 + 1");
    int64_t result = ex.eval();
    std::cout << result << std::endl;

or

    std::cout << expr3::expr3u("(1+1)*2 / (1+1)").eval() << std::endl;

Which outputs 2 for both cases.


The expression can be changed with `set_from_str()` at any time.
When an expression is constructed from a string, it is parsed into an intermediate format.
This speeds up repeated evaluations of the same expression (e.g. because it contains variables that changed).


expr3 supports all C++ operators, including assignment operators with their precedence as detailed in: https://en.cppreference.com/w/cpp/language/operator_precedence.
In addition expr3 supports rotate right / rotate left with "<<<" and ">>>". Note that rol/ror is not defined for signed integer types and implementation defined results are returned in such cases.

Arbitrarily nested parenthesis are supported. Bit-operators for floatingpoint-types operate on the raw bit-representation.



# Advanced usage

expr3 allows for some advanced features, notably custom variables and functions.
They are implemented by deriving from `expr3::expr_eval_context`.
By default the "default context" `expr3::default_expr_eval_context` is used.
It is recommended to derive from this context when writing a custom context.


## Variables and named constants

A variable is any non-integer identifier in the expression, for example "eax * 2".
Note that variable names must not parse as hex-numbers, or else they are interpreted as integer constants: 
"a + 1" evaluates to 0xB = 17 rather than resolving a variable named "a".
Variable names are not case sensitive. It is recommended, but not required, to prefix hex-constants with 0x for clarity.

The values of variables are queried for every subsequent eval() call anew.

The default context provides an exemplary variable PI with a constant value of the 3.1415.

The respective context-functions are `expr3::expr_eval_context::resolve_var_if_needed` for resolving variables and `expr3::expr_eval_context::assign` for assigning to them.


## Functions

A function consists of a function name followed by a list of parameters enclosed in parenthesis that are passed to the function: "max(param1,param2)". The parameters can be variables or constants. Variables are evaluated before being passed to the function.

The default context implements min(a,b) and max(a,b) as examples:

    uint64_t result = expr3::expr3u("min(8,16) / max(2,4)").eval();
    std::cout << result << std::endl;

The output is 8 / 4 = 2.

Functions can have an arbitrary amount of arguments and always return a constant.
If a variable is returned, it is evaluated prior to further processing.

Function names must not start with two underscores (__xxx), as such functions are reserved for internal use.

The context-function that handles executing functions is `expr3::expr_eval_context::exec_function`.


## Qt

If a Qt-environment is detected, an overload expr3qt is defined.
It works exactly like expr3, but offers convenience overloads for working with QString.

    using expr3s_qt = expr3qt<int64_t>;
    using expr3u_qt = expr3qt<uint64_t>;
    using expr3f_qt = expr3qt<double>;

## Deref

expr3 was originally designed for use in x86-heavy reverse engineering tools.
It thus supports a memory dereferencing operator natively: `[0x401000]` reads the word at address 0x401000.
Different size-specifiers are supported: byte (8bit), word (16bit), dword (32bit), qword (64bit) - analogous to x86 intel assembly (`"byte [0x401000] == 0"`).

The dereference operation is translated to a function call, which is handled in the context like any other function.