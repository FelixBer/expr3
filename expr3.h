#ifndef EXPR3_H
#define EXPR3_H

#include <string>
#include <sstream>
#include <vector>
#include <algorithm>
#include <cmath> //std::fmod

/*
  Implements and expression evaluatoin engine with the shunting yard algorithm.
  Complexity: O(n), n = length of expression.

  Can handle binary and unary operators, parentheses, variables, functions, composite functions, var-arg functions.
  Expressions can be pre-compiled for quicker evaluation.
  Variables are resolved via a context.
  Operator precedence follows the C++ specification.

  Resources:
  https://en.cppreference.com/w/cpp/language/operator_precedence
  https://en.wikipedia.org/wiki/Shunting-yard_algorithm
  http://reedbeta.com/blog/the-shunting-yard-algorithm/
*/

/*
 * todo:
 * - comma operator: function arg vs. eval?
 * - Make Token a proper variant and get rid of legacy cruft surrounding it.
 * - commit tests and examples
 */


namespace expr3 {


namespace {
    std::string u64_as_str(uint64_t val, int base)
    {
        std::stringstream stream;
        if(base == 16)
            stream << std::hex;
        else if(base == 10)
            stream << std::dec;
        else if(base == 8)
            stream << std::oct;
        else
            return "";

        stream << val;
        return stream.str();
        //return QString::number(val, base).toStdString();
    }
    std::string double_as_str(long double val)
    {
        std::stringstream stream;
        stream << std::fixed << val;
        return stream.str();
    }
    uint64_t str_as_u64(const std::string& str, bool* ok, int base)
    {
        try{
            size_t idx = 0;
            uint64_t r = std::stoull(str, &idx, base);
            if(ok)
                *ok = idx == str.size();
            if(idx != str.size())
                return 0;
            return r;
        } catch(const std::exception& ex) {
            if(ok)
                *ok = false;
            return 0;
        }
        //return QString::fromStdString(str).toULongLong(ok, base);
    }
    /*
     * Note: Qt messes with the locale, which makes std::stod fail on
     * "partly" configured e.g. german systems that use "," instead of ".".
     * Thus std::stod works before constructing QCoreApplication, but not after...
     * Taking it out of sstream seems to always work.
     */
    long double str_as_double(const std::string& str, bool* ok)
    {
        try{
            //size_t idx = 0;
            //std::cout << str << std::endl;
            //double r = std::stod(str, &idx);
            //std::cout << "ok!" << std::endl;
            //if(ok)
            //    *ok = idx == str.size();
            //if(idx != str.size())
            //    return 0;
            //return r;
            std::stringstream ss(str);
            long double d = 0.0;
            ss >> d;
            if(ok)
                *ok = true;
            return d;
        } catch(const std::exception& ex) {
            if(ok)
                *ok = false;
            return 0.0;
        }
    }
    //https://stackoverflow.com/questions/776508/best-practices-for-circular-shift-rotate-operations-in-c
    template <typename T>
    T rotl (T v, unsigned int b)
    {
      constexpr unsigned int num_bits {sizeof(T) * 8};
      constexpr unsigned int count_mask {num_bits - 1};
      const unsigned int mb {b & count_mask};
      return ((v << mb) | (v >> (-mb & count_mask)));
    }
    template <typename T>
    T rotr (T v, unsigned int b)
    {
      constexpr unsigned int num_bits {sizeof(T) * 8};
      constexpr unsigned int count_mask {num_bits - 1};
      const unsigned int mb {b & count_mask};
      return ((v >> mb) | (v << (-mb & count_mask)));
    }
    std::string tolower(std::string str)
    {
        std::transform(str.begin(), str.end(), str.begin(), [](unsigned char c){ return std::tolower(c); });
        return str;
    }
}


class Token;
class expr_eval_context
{
public:
    virtual ~expr_eval_context() = default;
    virtual Token resolve_var_if_needed(const Token& var) =0;
    virtual bool assign(const Token& dest, const Token& val) =0;
    virtual Token exec_function(const Token& func, std::vector<Token>& args) =0;
};

/*
 * Holds a typed text token.
 * The text token can be converted to an integer of type uint64_t.
 * Note that signed integers are returned as uint64_t and are casted
 * as apropriate in expr3::eval.
 * This technically violates C++ spec for integers over INT_MAX.
 *
 * Token is not a template and the value is stored as a string for legacy reasons.
 */
class Token {
public:
    enum class Type {
        Unknown = 0,
        Number,
        Function,
        FuncArgSeparator,
        Error,

        StrConstant,

        left_round_brace,   // (
        right_round_brace,  // )
        left_edge_brace,    // [
        right_edge_brace,   // ]
        comma,              // ,

        op_assign,          // =

        op_equal,           // ==
        op_not_equal,       // !=

        op_plus,            // +
        op_minus,           // -
        op_div,             // /
        op_mul,             // *
        op_bin_not,         // ~

        op_logical_not,     // !
        op_remainder,       // %
        op_logical_and,     // &&
        op_logical_or,      // ||
        op_binary_and,      // &
        op_binary_or,       // |
        op_binary_xor,      // ^

        op_cmd_small,       //<
        op_cmd_shl,         //<<
        op_cmd_rol,         //<<<
        op_cmd_smalleq,     //<=
        op_cmd_assign_shl,  //<<=
        op_cmd_assign_rol,  //<<<=

        op_cmd_big,         //>
        op_cmd_shr,         //>>
        op_cmd_ror,         //>>>
        op_cmd_bigeq,       //>=
        op_cmd_assign_shr,  //>>=
        op_cmd_assign_ror,  //>>>=

        op_assign_plus,       // +=
        op_assign_minus,      // -=
        op_assign_mul,        // *=
        op_assign_div,        // /=
        op_assign_remainder,  // %=
        op_assign_binary_and, // &=
        op_assign_binary_or,  // |=
        op_assign_binary_xor, // ^=


        op_assign_logical_and, // doesnt exist in C++/Java and is not implemented!
        op_assign_logical_or,  // doesnt exist in C++/Java and is not implemented!
        op_max,
    };

    enum class associativity {
        unknown_assoc = 0,
        right_assoc,
        left_assoc,
    };

    enum class op_type {
        unknown = 0,
        unary,
        binary,
    };

    Type type = Type::Unknown;
    op_type op_kind = op_type::unknown;
    std::string str;
    int precedence = -1;
    int size = 0;
    associativity assoc = associativity::unknown_assoc;
    int default_base = 16;

    Token() = default;
    Token(Type t, const std::string& s, int prec = -1, associativity ass = associativity::unknown_assoc)
        : type { t }, str { s }, precedence { prec }, assoc { ass }
    {
    }
    Token(uint64_t val)
    {
        type = Type::Number;
        str = u64_as_str(val, default_base);
    }
    Token(int64_t val) : Token(static_cast<uint64_t>(val))
    {
    }
    Token(bool val) : Token(static_cast<uint64_t>(val))
    {
    }
    Token(long double val)
    {
        type = Type::Number;
        str = double_as_str(val);
    }
    Token(double val) : Token(static_cast<long double>(val))
    {
    }


    static Token make_error(const std::string& msg)
    {
        return Token(Type::Error, msg);
    }

    static Token make_constant(uint64_t val)
    {
        return Token(Type::Number, u64_as_str(val, 16));
    }

    static Token make_double(double val)
    {
        return Token(Type::Number, double_as_str(val));
    }

    bool is_function() const { return type == Type::Function; }
    bool is_comma()    const { return type == Type::comma; }
    bool is_string()   const { return type == Type::StrConstant; }
    bool is_error()    const { return type == Type::Error; }
    bool is_valid()    const { return type != Type::Unknown && !is_error(); }
    bool is_number()   const { return type == Type::Number; }

    bool is_left_associative()  const { return assoc == associativity::left_assoc;  }
    bool is_right_associative() const { return assoc == associativity::right_assoc; }

    bool is_op() const
    {
        switch(type)
        {
            case Type::op_equal: case Type:: op_not_equal:
            case Type::op_plus:  case Type::op_minus: case Type::op_mul: case Type::op_div: case Type::op_remainder:

            case Type::op_bin_not:     case Type::op_logical_not:
            case Type::op_logical_and: case Type::op_logical_or:
            case Type::op_binary_and:  case Type::op_binary_or:  case Type::op_binary_xor:

            case Type::op_cmd_small: case Type::op_cmd_shl: case Type::op_cmd_rol:case Type::op_cmd_smalleq:
            case Type::op_cmd_big:   case Type::op_cmd_shr: case Type::op_cmd_ror:case Type::op_cmd_bigeq:

            case Type::op_assign:
            case Type::op_cmd_assign_ror:     case Type::op_cmd_assign_shr:
            case Type::op_cmd_assign_rol:     case Type::op_cmd_assign_shl:
            case Type::op_assign_plus:        case Type::op_assign_minus:
            case Type::op_assign_mul:         case Type::op_assign_div:
            case Type::op_assign_remainder:   case Type::op_assign_binary_and:
            case Type::op_assign_binary_or:   case Type::op_assign_binary_xor:
                return true;
            default:
                return false;
        }
    }

    bool is_op_binary() const
    {
        return op_kind == op_type::binary;
    }

    bool is_op_unary() const
    {
        return op_kind == op_type::unary;
    }

    uint64_t as_integer() const
    {
        uint64_t vali = 0;
        if(is_integer(&vali))
            return vali;
        double valf = 0.0;
        if(is_double(&valf))
            return static_cast<uint64_t>(valf);
        return 0; //shouldn happen
    }

    double as_double() const
    {
        double valf = 0.0;
        if(is_double(&valf))
            return valf;
        uint64_t vali = 0;
        if(is_integer(&vali))
            return static_cast<double>(vali);
        return 0.0; //shouldn happen
    }

    bool is_integer(uint64_t* out = nullptr) const
    {
        bool ok;
        auto val = str_as_u64(str, &ok, default_base);
        if(ok && out)
            *out = val;
        if(!ok)
        {
            val = str_as_u64(str, &ok, 16);
            if(ok && out)
                *out = val;
            if(!ok)
            {
                val = str_as_u64(str, &ok, 10);
                if(ok && out)
                    *out = val;
            }
        }
        return ok;
    }

    bool is_double(double* out = nullptr) const
    {
        bool ok1 = (str.find('.') != std::string::npos) || (str.find(',') != std::string::npos);
        bool ok2;
        auto val = str_as_double(str, &ok2);
        if(out)
            *out = val; //even if conversion failed, we set it to 0.0
        return ok1 && ok2;
    }

    //https://en.cppreference.com/w/cpp/language/operator_precedence
    static Token create_from_type(Type t)
    {
        const auto left  = associativity::left_assoc;
        const auto right = associativity::right_assoc;
        switch(t)
        {

            case Type::op_bin_not:          return Token(t, "~",     3, right);
            case Type::op_logical_not:      return Token(t, "!",     3, right);

            case Type::op_binary_and:       return Token(t, "&",     11, left);
            case Type::op_binary_xor:       return Token(t, "^",     12, left);
            case Type::op_binary_or:        return Token(t, "|",     13, left);
            case Type::op_logical_and:      return Token(t, "&&",    14, left);
            case Type::op_logical_or:       return Token(t, "||",    15, left);

            case Type::op_equal:            return Token(t, "==",   10, left);
            case Type::op_not_equal:        return Token(t, "!=",   10, left);
            case Type::op_plus:             return Token(t, "+",     6, left);
            case Type::op_minus:            return Token(t, "-",     6, left);
            case Type::op_mul:              return Token(t, "*",     5, left);
            case Type::op_div:              return Token(t, "/",     5, left);
            case Type::op_remainder:        return Token(t, "%",     5, left);

            case Type::op_cmd_shl:          return Token(t, "<<",    7, left);
            case Type::op_cmd_rol:          return Token(t, "<<<",   7, left);
            case Type::op_cmd_small:        return Token(t, "<",     9, left);
            case Type::op_cmd_smalleq:      return Token(t, "<=",    9, right);

            case Type::op_cmd_shr:          return Token(t, ">>",    7, left);
            case Type::op_cmd_ror:          return Token(t, ">>>",   7, left);
            case Type::op_cmd_big:          return Token(t, ">",     9, left);
            case Type::op_cmd_bigeq:        return Token(t, ">=",    9, right);

            case Type::op_assign:           return Token(t, "=",    16, right);
            case Type::op_cmd_assign_shl:   return Token(t, "<<=",  16, right);
            case Type::op_cmd_assign_rol:   return Token(t, "<<<=", 16, right);
            case Type::op_cmd_assign_shr:   return Token(t, ">>=",  16, right);
            case Type::op_cmd_assign_ror:   return Token(t, ">>>=", 16, right);
            case Type::op_assign_plus:      return Token(t, "+=",   16, right);
            case Type::op_assign_minus:     return Token(t, "-=",   16, right);
            case Type::op_assign_mul:       return Token(t, "*=",   16, right);
            case Type::op_assign_div:       return Token(t, "/=",   16, right);
            case Type::op_assign_remainder: return Token(t, "%=",   16, right);
            case Type::op_assign_binary_and:return Token(t, "&=",   16, right);
            case Type::op_assign_binary_or: return Token(t, "|=",   16, right);
            case Type::op_assign_binary_xor:return Token(t, "^=",   16, right);

            case Type::left_round_brace:    return Token(t, "(",    -1, left);
            case Type::right_round_brace:   return Token(t, ")",    -1, left);
            case Type::left_edge_brace:     return Token(t, "[",    -1, left);
            case Type::right_edge_brace:    return Token(t, "]",    -1, left);
            case Type::comma:               return Token(t, ",",    17, left);
            case Type::FuncArgSeparator:    return Token(t, "#");
            default:
                return Token();
        }
    }
};





class default_expr_eval_context : public expr_eval_context
{
public:
    Token resolve_var_if_needed(const Token& var) override
    {
        if(var.str == "pi")
            return 3.1415926535;
        return var;
    }
    bool assign(const Token& dest, const Token& val) override
    {
        return true;
    }
    Token exec_function(const Token& func, std::vector<Token>& args) override
    {
        if(func.type != Token::Type::Function)
            return {};

        if(func.str == "__deref")
        {
            if(args.empty())
                return {};
            int size = func.size;
            if(size == -1)
            {
                size = 8; //todo: select right one...
            }
            auto adr = args.back().as_integer();
            //memread(adr,tok.size)
            return Token::make_constant(0x33333333);
        }
        else if(func.str == "max")
        {
            if(args.size() < 2)
                return false;

            Token op1 = args[0];
            Token op2 = args[1];
            Token res;

            if(op1.is_double() || op2.is_double())
                res = Token::make_double(std::max(op1.as_double(), op2.as_double()));
            else
                res = Token::make_constant(std::max(op1.as_integer(), op2.as_integer()));
            return res;
        }
        else if(func.str == "min")
        {
            if(args.size() < 2)
                return false;

            Token op1 = args[0];
            Token op2 = args[1];
            Token res;

            if(op1.is_double() || op2.is_double())
                res = Token::make_double(std::min(op1.as_double(), op2.as_double()));
            else
                res = Token::make_constant(std::min(op1.as_integer(), op2.as_integer()));
            return res;
        }

        return {};
    }
};

template<typename integer_type>
class expr3
{
    enum error_type {
        no_error = 0,
        parens_mismatch = 1,
        operator_mismatch = 2,
        other_error = 4,
        internal_error = 8,
        eval_stack_error = 16,
        function_or_deref_error = 32,
        assignment_error = 64,
    };

protected:
    std::vector<Token> data;
    std::string expr;

public:
    expr3() = default;
    expr3(const std::string& expression)
    {
        set_from_string(expression);
    }

    Token set_from_string(const std::string& expression)
    {
        expr = expression;
        data = tokenize(expr);
        pre_process(data);
        data = shunting_yard(data);
        if(data.size() && data.back().is_error())
        {
            Token r = data.back();
            data.clear();
            return r;
        }
        return data.empty();
    }

    std::string intermediate_repr() const
    {
        std::string r;
        for(const auto& t : data)
            r += t.str + ' ';
        return r;
    }

    std::string string_repr() const
    {
        return expr;
    }

    integer_type eval(bool* success = nullptr, expr_eval_context* context = nullptr) const
    {
        default_expr_eval_context dc;
        if(context == nullptr)
            context = &dc;
        Token final = eval(data, context);
        if(success)
            *success = final.is_number();
        if(final.is_double())
            return static_cast<integer_type>(final.as_double());
        return static_cast<integer_type>(final.as_integer());
    }

    static std::vector<Token> tokenize(const std::string& str)
    {
        std::vector<Token> tokens;

        const auto peek_grab_char_if = [&](size_t& i, char c) {
            if(i+1 < str.length())
            {
                if(str[i+1] == c)
                {
                    i++;
                    return true;
                }
            }
            return false;
        };

        bool grab_string = false;
        std::string cur_data;

        const auto add_operator = [&](Token::Type t) {
            if(cur_data.size())
            {
                tokens.push_back(Token(Token::Type::Number, cur_data));
                cur_data.clear();
            }
            tokens.push_back(Token::create_from_type(t));
        };

        for(size_t i = 0; i < str.size(); i++)
        {
            const char ch = str.at(i);
            if(ch == '"')
            {
                if(grab_string)
                {
                    tokens.push_back(Token(Token::Type::StrConstant, cur_data));
                    cur_data.clear();
                }
                grab_string = !grab_string;
            }
            else if(grab_string)
            {
                cur_data.push_back(ch);
            }
            else if(ch == ' ')
            {
                if(cur_data.size())
                {
                    tokens.push_back(Token(Token::Type::Number, cur_data));
                    cur_data.clear();
                }
            }
            else
            {
                switch(ch)
                {
                    case '.':
                    default:  cur_data.push_back(ch); break;

                    case '+':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_assign_plus);
                        else
                            add_operator(Token::Type::op_plus);
                        break;
                    case '-':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_assign_minus);
                        else
                            add_operator(Token::Type::op_minus);
                        break;
                    case '*':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_assign_mul);
                        else
                            add_operator(Token::Type::op_mul);
                        break;
                    case '/':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_assign_div);
                        else
                            add_operator(Token::Type::op_div);
                        break;
                    case '%':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_assign_remainder);
                        else
                            add_operator(Token::Type::op_remainder);
                        break;
                    case '^':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_assign_binary_xor);
                        else
                            add_operator(Token::Type::op_binary_xor);
                        break;
                    case '~': add_operator(Token::Type::op_bin_not);        break;
                    case '(': add_operator(Token::Type::left_round_brace);  break;
                    case ')': add_operator(Token::Type::right_round_brace); break;
                    case '[': add_operator(Token::Type::left_edge_brace);   break;
                    case ']': add_operator(Token::Type::right_edge_brace);  break;
                    case ',': add_operator(Token::Type::comma);             break;
                    case '|':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_assign_binary_or); // |=
                        else
                            add_operator(Token::Type::op_binary_or);
                        break;
                    case '&':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_assign_binary_and); // &=
                        else
                            add_operator(Token::Type::op_binary_and);
                        break;
                    case '=':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_equal);
                        else
                            add_operator(Token::Type::op_assign);
                        break;
                    case '!':
                        if(peek_grab_char_if(i, '='))
                            add_operator(Token::Type::op_not_equal);
                        else
                            add_operator(Token::Type::op_logical_not);
                        break;
                    case '<':
                        if(peek_grab_char_if(i, '<'))
                        {
                            if(peek_grab_char_if(i, '<'))
                            {
                                if(peek_grab_char_if(i, '='))
                                    add_operator(Token::Type::op_cmd_assign_rol);
                                else
                                    add_operator(Token::Type::op_cmd_rol);
                            }
                            else
                            {
                                if(peek_grab_char_if(i, '='))
                                    add_operator(Token::Type::op_cmd_assign_shl);
                                else
                                    add_operator(Token::Type::op_cmd_shl);
                            }
                        }
                        else
                        {
                            if(peek_grab_char_if(i, '='))
                                add_operator(Token::Type::op_cmd_smalleq);
                            else
                                add_operator(Token::Type::op_cmd_small);
                        }
                        break;
                    case '>':
                        if(peek_grab_char_if(i, '>'))
                        {
                            if(peek_grab_char_if(i, '>'))
                            {
                                if(peek_grab_char_if(i, '='))
                                    add_operator(Token::Type::op_cmd_assign_ror);
                                else
                                    add_operator(Token::Type::op_cmd_ror);
                            }
                            else
                            {
                                if(peek_grab_char_if(i, '='))
                                    add_operator(Token::Type::op_cmd_assign_shr);
                                else
                                    add_operator(Token::Type::op_cmd_shr);
                            }
                        }
                        else
                        {
                            if(peek_grab_char_if(i, '='))
                                add_operator(Token::Type::op_cmd_bigeq);
                            else
                                add_operator(Token::Type::op_cmd_big);
                        }
                        break;
                }
            }
        }

        if(cur_data.size())
        {
            tokens.push_back(Token(Token::Type::Number, cur_data));
            cur_data.clear();
        }
        return tokens;
    }

    //normalizes derefs, functions, binary-vs-unary operators, ...
    static void pre_process(std::vector<Token>& tokens)
    {
        //size qualifiers
        //patch [] deref accessor with __deref() function call
        for(size_t i=0; i < tokens.size(); i++)
        {
            if(tokens[i].type == Token::Type::left_edge_brace)
            {
                tokens[i] = Token::create_from_type(Token::Type::left_round_brace);
                if(i != 0 && tokens[i-1].type == Token::Type::Number)
                {
                    const std::string str = tolower(tokens[i-1].str);
                    if(str == "byte")
                        tokens[i-1].size = 1;
                    else if(str == "word")
                        tokens[i-1].size = 2;
                    else if(str == "dword")
                        tokens[i-1].size = 4;
                    else if(str == "qword")
                        tokens[i-1].size = 8;

                    tokens[i-1].type = Token::Type::Function;
                    tokens[i-1].str = "__deref";
                }
                else
                {
                    //we have to insert a size qualifier
                    Token t(Token::Type::Function, "__deref");
                    t.size = -1;
                    tokens.insert(tokens.begin() + int(i), t);
                }
            }
            else if(tokens[i].type == Token::Type::right_edge_brace)
            {
                tokens[i] = Token::create_from_type(Token::Type::right_round_brace);
            }
        }

        //function call vs. simple parens
        for(size_t i=0; i < tokens.size(); i++)
        {
            if(tokens[i].type == Token::Type::Number && !tokens[i].is_integer() && !tokens[i].is_double() && i != tokens.size()-1)
                if(tokens[i+1].type == Token::Type::left_round_brace)
                    tokens[i].type = Token::Type::Function;
        }

        //binary vs. unary op
        for(size_t i=0; i < tokens.size(); i++)
        {
            Token& tok = tokens[i];
            if(tok.is_op())
            {
                if(i == 0)
                    tok.op_kind = Token::op_type::unary; //if nothing before -> unary
                else if(tokens[i-1].type == Token::Type::Number)
                    tok.op_kind = Token::op_type::binary; // if number before -> binary
                else if(tokens[i-1].type == Token::Type::right_round_brace)
                    tok.op_kind = Token::op_type::binary; // if closing/right parens -> binary
                else
                    tok.op_kind = Token::op_type::unary;// if any other operator or open/left parens -> unary
            }
        }

        tokens.erase(std::remove_if(tokens.begin(), tokens.end(),
                [](const Token& o) { return !o.is_valid(); }),
            tokens.end());
    }

    static std::vector<Token> shunting_yard(const std::vector<Token>& tokens)
    {
        std::vector<Token> stack, output;
        stack.reserve(tokens.size());
        output.reserve(tokens.size());
        uint err=0;

        for(const auto& tok : tokens)
        {
            if(tok.type == Token::Type::Function)
            {
                output.push_back(Token::create_from_type(Token::Type::FuncArgSeparator));
                stack.push_back(tok);
            }
            else if(tok.type == Token::Type::Number)
            {
                output.push_back(tok);
            }
            else if(tok.type == Token::Type::comma)
            {
                while(stack.size() && stack.back().type != Token::Type::left_round_brace)
                {
                    output.push_back(stack.back());
                    stack.pop_back();
                }
                //output.push_back(tok);
            }
            else if(tok.is_op())
            {
                while(stack.size()
                      && ((stack.back().precedence < tok.precedence)
                          || (stack.back().precedence == tok.precedence && stack.back().is_left_associative())
                          || stack.back().type == Token::Type::Function)
                      && (stack.back().type != Token::Type::left_round_brace))
                {
                    if(tok.is_op_unary() && stack.back().is_op_binary()) //a unary operator never pops a binary one!
                        break;
                    output.push_back(stack.back());
                    stack.pop_back();
                }
                stack.push_back(tok);
            }
            else if(tok.type == Token::Type::left_round_brace)
            {
                stack.push_back(tok);
            }
            else if(tok.type == Token::Type::right_round_brace)
            {
                while(stack.size() && stack.back().type != Token::Type::left_round_brace)
                {
                    output.push_back(stack.back());
                    stack.pop_back();
                }

                if(stack.size() == 0)
                {
                    //error mismatching parens
                    err |= error_type::parens_mismatch;
                    return { Token::make_error("Parens mismatch.") };
                }

                stack.pop_back(); //remove ( from stack

                //if it was a function call, push function to output
                if(stack.size() && stack.back().type == Token::Type::Function)
                {
                    output.push_back(stack.back());
                    stack.pop_back();
                }
            }
        }

        while(stack.size())
        {
            if(stack.back().type == Token::Type::left_round_brace || stack.back().type == Token::Type::right_round_brace)
            {
                //error mismatching ( or )
                err |= error_type::parens_mismatch;
                return { Token::make_error("Parens mismatch.") };
            }
            output.push_back(stack.back());
            stack.pop_back();
        }

        return output;
    }

    static Token eval(const std::vector<Token>& expr, expr_eval_context* context)
    {
        std::vector<Token> stack;
        uint err=0;

        for(const auto& tok : expr)
        {
            if(tok.type == Token::Type::Function)
            {
                std::vector<Token> args;
                while(stack.size() && stack.back().type != Token::Type::FuncArgSeparator)
                {
                    //evaluate the variables, this also means we always pass by (evaluated) value, not reference
                    Token t = context->resolve_var_if_needed(stack.back());
                    args.push_back(t);
                    stack.pop_back();
                }
                if(stack.size() == 0)
                {
                    //error: func arg separator not found! internal error!
                    err |= error_type::internal_error;
                    return Token::make_error("Internal error. func_arg_sep not found.");
                }
                stack.pop_back(); //remove func arg separator

                //execute function
                std::reverse(args.begin(), args.end()); //stack order -> logical order

                Token r = context->exec_function(tok, args);
                if(!r.is_valid())
                {
                    err |= error_type::function_or_deref_error;
                    return Token::make_error("Error in function or on dereferencing.");
                }
                stack.push_back(r); //set return value
            }
            else if(tok.is_op())
            {
                /*
                 evaluation of the variables is done inside eval_op so we can handle assignments more cleanly
                */
                if(tok.is_op_binary())
                {
                    if(stack.size() < 2)
                    {
                        //error, not possible
                        err |= error_type::eval_stack_error;
                        return Token::make_error("Stack depth error on binary operator.");
                    }

                    const Token right = stack.back();
                    stack.pop_back();
                    const Token left = stack.back();
                    stack.pop_back();

                    Token res = eval_op(tok.type, left, right, context);
                    stack.push_back(res);
                }
                else if(tok.is_op_unary())
                {
                    if(stack.size() < 1)
                    {
                        //error, not possible
                        err |= error_type::eval_stack_error;
                        return Token::make_error("Stack depth error on unary operator.");
                    }

                    const Token right = stack.back();
                    const Token left = {};
                    stack.pop_back();

                    Token res = eval_op(tok.type, left, right, context);
                    stack.push_back(res);
                }
            }
            else
            {
                stack.push_back(tok);
            }
        }

        if(stack.size() != 1)
        {
            //error
            err |= error_type::eval_stack_error;
            return Token::make_error("Stack depth error on finalization.");
        }

        Token final = context->resolve_var_if_needed(stack.back());
        return final;
    }

    /*
     Evaluates two constants according to operator op.
     INTEGER
     */
    template<typename T = integer_type,typename std::enable_if<std::is_integral<T>::value,bool>::type = true>
    static Token eval_op(Token::Type op, Token left, Token right, expr_eval_context* context)
    {
        static_assert(std::is_same<T,integer_type>::value, "Token::eval_op specialization mismatch");
        const Token original_left = left;

        //assert(context != nullptr)
        if(left.is_valid())
            left  = context->resolve_var_if_needed(left);
        if(right.is_valid())
            right = context->resolve_var_if_needed(right);

        //see notes for Token::Token
        const integer_type li = static_cast<integer_type>(left.as_integer());
        const integer_type ri = static_cast<integer_type>(right.as_integer());

        Token evaluated;
        switch(op)
        {
            case Token::Type::StrConstant:
            case Token::Type::Number:
            case Token::Type::left_round_brace:
            case Token::Type::right_round_brace:
            case Token::Type::left_edge_brace:
            case Token::Type::right_edge_brace:
            default:
                return {};
            case Token::Type::op_logical_and:      return li && ri;
            case Token::Type::op_logical_or:       return li || ri;
            case Token::Type::op_binary_and:       return li &  ri;
            case Token::Type::op_binary_or:        return li |  ri;
            case Token::Type::op_binary_xor:       return li ^  ri;
            case Token::Type::op_equal:            return li == ri;
            case Token::Type::op_not_equal:        return li != ri;
            case Token::Type::op_bin_not:          return ~ri;
            case Token::Type::op_logical_not:      return !ri;
            case Token::Type::op_plus:             return li +  ri;
            case Token::Type::op_minus:            return li -  ri;
            case Token::Type::op_div:              return li /  ri;
            case Token::Type::op_mul:              return li *  ri;
            case Token::Type::op_remainder:        return li %  ri;
            case Token::Type::op_cmd_small:        return li <  ri;
            case Token::Type::op_cmd_shl:          return li << ri;
            case Token::Type::op_cmd_rol:          return rotl(li, ri);
            case Token::Type::op_cmd_smalleq:      return li <= ri;
            case Token::Type::op_cmd_big:          return li >  ri;
            case Token::Type::op_cmd_shr:          return li >> ri;
            case Token::Type::op_cmd_ror:          return rotr(li, ri);
            case Token::Type::op_cmd_bigeq:        return li >= ri;

            case Token::Type::op_assign:             evaluated = ri;        break;
            case Token::Type::op_cmd_assign_shl:     evaluated = li << ri;  break;
            case Token::Type::op_cmd_assign_rol:     evaluated = rotl(li, ri);  break;
            case Token::Type::op_cmd_assign_shr:     evaluated = li >> ri;  break;
            case Token::Type::op_cmd_assign_ror:     evaluated = rotr(li, ri);  break;
            case Token::Type::op_assign_plus:        evaluated = li +  ri;  break;
            case Token::Type::op_assign_minus:       evaluated = li -  ri;  break;
            case Token::Type::op_assign_mul:         evaluated = li *  ri;  break;
            case Token::Type::op_assign_div:         evaluated = li /  ri;  break;
            case Token::Type::op_assign_remainder:   evaluated = li %  ri;  break;
            case Token::Type::op_assign_binary_and:  evaluated = li &  ri;  break;
            case Token::Type::op_assign_binary_or:   evaluated = li |  ri;  break;
            case Token::Type::op_assign_binary_xor:  evaluated = li ^  ri;  break;
        }

        //assert(target.is_valid())
        if(!context->assign(original_left, evaluated))
            return Token::make_error("error during assignment"); //err |= error_type::assignment_error;
        return original_left;
    }

    /*
     Evaluates two constants according to operator op.
     FLOAT
     */
    template<typename T = integer_type,typename std::enable_if<std::is_floating_point<T>::value,bool>::type = true>
    static Token eval_op(Token::Type op, Token left, Token right, expr_eval_context* context)
    {
        static_assert(std::is_same<T,integer_type>::value, "Token::eval_op specialization mismatch");
        const Token original_left = left;

        //assert(context != nullptr)
        if(left.is_valid())
            left  = context->resolve_var_if_needed(left);
        if(right.is_valid())
            right = context->resolve_var_if_needed(right);

        //see notes for Token::Token
        const integer_type li = static_cast<integer_type>(left.as_double());
        const integer_type ri = static_cast<integer_type>(right.as_double());

        Token evaluated;
        switch(op)
        {
            case Token::Type::StrConstant:
            case Token::Type::Number:
            case Token::Type::left_round_brace:
            case Token::Type::right_round_brace:
            case Token::Type::left_edge_brace:
            case Token::Type::right_edge_brace:
            default:
                return {};
            case Token::Type::op_logical_and:      return li && ri;
            case Token::Type::op_logical_or:       return li || ri;
            case Token::Type::op_binary_and:       return static_cast<integer_type>(static_cast<uint64_t>(li) & static_cast<uint64_t>(ri));
            case Token::Type::op_binary_or:        return static_cast<integer_type>(static_cast<uint64_t>(li) | static_cast<uint64_t>(ri));
            case Token::Type::op_binary_xor:       return static_cast<integer_type>(static_cast<uint64_t>(li) ^ static_cast<uint64_t>(ri));
            case Token::Type::op_equal:            return li == ri;
            case Token::Type::op_not_equal:        return li != ri;
            case Token::Type::op_bin_not:          return static_cast<integer_type>(~static_cast<uint64_t>(li));
            case Token::Type::op_logical_not:      return !li;
            case Token::Type::op_plus:             return li +  ri;
            case Token::Type::op_minus:            return li -  ri;
            case Token::Type::op_div:              return li /  ri;
            case Token::Type::op_mul:              return li *  ri;
            case Token::Type::op_remainder:        return std::fmod(li, ri);
            case Token::Type::op_cmd_small:        return li <  ri;
            case Token::Type::op_cmd_shl:          return static_cast<integer_type>(static_cast<uint64_t>(li) << static_cast<uint64_t>(ri));
            case Token::Type::op_cmd_rol:          return static_cast<integer_type>(rotl(static_cast<uint64_t>(li), static_cast<unsigned int>(ri)));
            case Token::Type::op_cmd_smalleq:      return li <= ri;
            case Token::Type::op_cmd_big:          return li >  ri;
            case Token::Type::op_cmd_shr:          return static_cast<integer_type>(static_cast<uint64_t>(li) >> static_cast<uint64_t>(ri));
            case Token::Type::op_cmd_ror:          return static_cast<integer_type>(rotr(static_cast<uint64_t>(li), static_cast<unsigned int>(ri)));
            case Token::Type::op_cmd_bigeq:        return li >= ri;

            case Token::Type::op_assign:             evaluated = ri;        break;
            case Token::Type::op_cmd_assign_shl:     evaluated = static_cast<integer_type>(static_cast<uint64_t>(li) << static_cast<uint64_t>(ri));  break;
            case Token::Type::op_cmd_assign_rol:     evaluated = static_cast<integer_type>(rotl(static_cast<uint64_t>(li), static_cast<unsigned int>(ri)));  break;
            case Token::Type::op_cmd_assign_shr:     evaluated = static_cast<integer_type>(static_cast<uint64_t>(li) >> static_cast<uint64_t>(ri));;  break;
            case Token::Type::op_cmd_assign_ror:     evaluated = static_cast<integer_type>(rotr(static_cast<uint64_t>(li), static_cast<unsigned int>(ri)));  break;
            case Token::Type::op_assign_plus:        evaluated = li +  ri;  break;
            case Token::Type::op_assign_minus:       evaluated = li -  ri;  break;
            case Token::Type::op_assign_mul:         evaluated = li *  ri;  break;
            case Token::Type::op_assign_div:         evaluated = li /  ri;  break;
            case Token::Type::op_assign_remainder:   evaluated = static_cast<integer_type>(static_cast<uint64_t>(li) % static_cast<uint64_t>(ri));  break;
            case Token::Type::op_assign_binary_and:  evaluated = static_cast<integer_type>(static_cast<uint64_t>(li) & static_cast<uint64_t>(ri));  break;
            case Token::Type::op_assign_binary_or:   evaluated = static_cast<integer_type>(static_cast<uint64_t>(li) | static_cast<uint64_t>(ri));  break;
            case Token::Type::op_assign_binary_xor:  evaluated = static_cast<integer_type>(static_cast<uint64_t>(li) ^ static_cast<uint64_t>(ri));  break;
        }

        //assert(target.is_valid())
        if(!context->assign(original_left, evaluated))
            return Token::make_error("error during assignment"); //err |= error_type::assignment_error;
        return original_left;
    }
};


using expr3s = expr3<int64_t>;
using expr3u = expr3<uint64_t>;
using expr3f = expr3<double>;


} //namespace expr3


#ifdef QT_CORE_LIB
#include <QString>

namespace expr3 {
    template<typename integer_type>
    class expr3qt : public expr3<integer_type>
    {
    public:
        expr3qt() = default;
        expr3qt(const std::string& expression) : expr3<integer_type>(expression) {}
        expr3qt(const QString& expression) : expr3qt(expression.toStdString()) {}

        Token set_from_string(const QString& expression)
        {
            return set_from_string(expression.toStdString());
        }
        using expr3<integer_type>::set_from_string;

        QString intermediate_repr_qt() const
        {
            return QString::fromStdString(expr3<integer_type>::intermediate_repr());
        }

        QString string_repr_qt() const
        {
            return QString::fromStdString(expr3<integer_type>::string_repr());
        }
    };

using expr3s_qt = expr3qt<int64_t>;
using expr3u_qt = expr3qt<uint64_t>;
using expr3f_qt = expr3qt<double>;
} //expr3
#endif //QT





#endif // EXPR3_H
