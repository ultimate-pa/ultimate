#!/usr/bin/python3
import re
import os
import sys
import datetime

##########################################################################################
# S-Expression parsing code taken from https://rosettacode.org/wiki/S-expressions#Python #
##########################################################################################

dbg = False
term_regex = r'''(?mx)
    \s*(?:
        (?P<brackl>\()|
        (?P<brackr>\))|
        (?P<num>\-?\d+\.\d+|\-?\d+)|
        (?P<sq>"[^"]*")|
        (?P<s>[^(^)\s]+)
       )'''

def parse_sexps(sexp):
    stack = []
    out = []
    if dbg: print("%-6s %-14s %-44s %-s" % tuple("term value out stack".split()))
    for termtypes in re.finditer(term_regex, sexp):
        term, value = [(t,v) for t,v in termtypes.groupdict().items() if v][0]
        if dbg: print("%-7s %-14s %-44r %-r" % (term, value, out, stack))
        if   term == 'brackl':
            stack.append(out)
            out = []
        elif term == 'brackr':
            assert stack, "Trouble with nesting of brackets"
            tmpout, out = out, stack.pop(-1)
            out.append(tmpout)
        elif term == 'num':
            v = float(value)
            if v.is_integer(): v = int(v)
            out.append(v)
        elif term == 'sq':
            out.append(value[1:-1])
        elif term == 's':
            out.append(value)
        else:
            raise NotImplementedError("Parse Error: %r" % (term, value))
    assert not stack, "Trouble with nesting of brackets"
    return out

def print_sexp(exp):
    out = ''
    if type(exp) == type([]):
        out += '(' + ' '.join(print_sexp(x) for x in exp) + ')'
    elif type(exp) == type('') and re.search(r'[\s()]', exp):
        out += '"%s"' % repr(exp)[1:-1].replace('"', '\"')
    else:
        out += '%s' % exp
    return out

##########################################################################################
# Code to translate weaver syntax to Boogie.                                             #
# Author: Dominik Klumpp                                                                 #
##########################################################################################

use_join_trick = True

def translate(sexps, max_thread):
    (stmts, globals, methods, _) = translate_seq(sexps, {}, 1, "  ")
    return (stmts, globals, methods)

def translate_clause(clause, globals, max_thread, indent):
    # return (stmts, glob, meth, max)
    kind, *args = clause
    if kind == 'var':
        return ("", translate_var(args), [], max_thread)
    elif kind == 'declare':
        assert len(args) >= 2, "'declare' with unexpected arguments: %r" % args
        return translate_declare(args[0], args[1:], globals, max_thread, indent)
    elif kind == 'assume':
        assert len(args) == 1
        return (indent + translate_assume(args[0], globals), {}, [], max_thread)
    elif kind == 'set!':
        assert len(args) == 2
        return (indent + translate_assign(args[0], args[1], globals), {}, [], max_thread)
    elif kind == 'store!':
        assert len(args) == 3
        return (indent + translate_store_stmt(args[0], args[1], args[2], globals), {}, [], max_thread)
    elif kind == 'havoc!':
        assert len(args) == 1
        return (indent + translate_havoc(args[0], globals), {}, [], max_thread)
    elif kind == 'atomic':
        return translate_atomic(args, globals, max_thread, indent)
    elif kind == 'cond':
        return translate_alt(args, globals, max_thread, indent)
    elif kind == 'if':
        assert len(args) == 2 or len(args) == 3, "encountered if with %d arguments: %r" % (len(args), args)
        return translate_if(args[0], args[1], args[2] if len(args) == 3 else None, globals, max_thread, indent)
    elif kind == 'while':
        assert len(args) >= 2, "encountered while with %d arguments: %r" % (len(args), args)
        return translate_while(args[0], args[1:], globals, max_thread, indent)
    elif kind == 'loop':
        assert len(args) >= 1
        return translate_loop(args, globals, max_thread, indent)
    elif kind == 'seq':
        return translate_seq(args, globals, max_thread, indent)
    elif kind == 'par':
        return translate_par(args, globals, max_thread, indent)
    elif kind == 'replicate':
        assert len(args) == 2
        return translate_replicate(args[0], args[1], globals, max_thread, indent)
    elif kind == 'use':
        # USE seems to give hints to the verifier. We ignore this here.
        return ("", {}, [], max_thread)
    else:
        raise NotImplementedError("Unknown clause: %s" % kind)

def translate_each_clause(clauses, globals, max_thread, indent):
    code = []
    new_globals = {}
    methods = []

    for clause in clauses:
        (stmts, glob, meth, max_thread) = translate_clause(clause, globals, max_thread, indent)
        code = code + [stmts]
        new_globals = {**new_globals, **glob}
        methods = methods + meth

    return (code, new_globals, methods, max_thread)

def translate_var(args):
    names = []
    typeindices = []
    for i, name in enumerate(args, start=1):
        if i == len(args):
            basetype = name
        elif isinstance(name, list):
            typeindices = typeindices + name
        else:
            names = names + [escape_id(name)]

    if len(typeindices) == 0:
        type = basetype
    else:
        type = (typeindices, basetype)
    return { name: type for name in names }

def translate_declare(var, body, globals, max_thread, indent):
    decls = translate_var(var)
    (code, glob, meth, max_thread) = translate_seq(body, globals, max_thread, indent)
    new_code = "\n".join([ indent + print_decl(d[0], d[1]) for d in decls.items()]) + code
    return (new_code, glob, meth, max_thread)

def translate_assume(formula, globals):
    return "assume %s;\n" % translate_expr(formula, globals)

def translate_assign(lhs, rhs, globals):
    return "%s := %s;\n" % (translate_expr(lhs, globals), translate_expr(rhs, globals))

def translate_store_stmt(arr, index, val, globals):
    return translate_assign(["select", arr, index], val, globals)

def translate_havoc(var, globals):
    return "havoc %s;\n" % translate_expr(var, globals)

def translate_atomic(body, globals, max_thread, indent):
    (code, new_globals, methods, max_thread) = translate_seq(body, globals, max_thread, indent + "  ")
    return (indent + "atomic {\n" + code + indent + "}\n", new_globals, methods, max_thread)

def translate_replicate(num, body, globals, max_thread, indent):
    return translate_par([body] * num, globals, max_thread, indent)

def translate_par(threads, globals, max_thread, indent):
    new_globals = {}
    methods = []
    forks = ""
    joins = ""

    for thread in threads:
        name = 'thread%d' % max_thread
        if use_join_trick:
            thread_id = ",".join([str(max_thread)] * max_thread)
        else:
            thread_id = str(max_thread)
        forks = forks + indent + ("fork %s %s();\n" % (thread_id, name))
        joins = joins + indent + ("join %s;\n" % thread_id)
        (body, glob, meth, max_thread) = translate_clause(thread, globals, max_thread + 1, "  ")
        new_globals = {**new_globals, **glob}
        methods = methods + meth + [(name, body)]

    return (forks + joins, new_globals, methods, max_thread)

def translate_seq(commands, globals, max_thread, indent):
    new_globals = {}
    methods = []
    code = ""

    for cmd in commands:
        (stmts, glob, meth, max_thread) = translate_clause(cmd, {**globals, **new_globals}, max_thread, indent)
        code = code + stmts
        new_globals = {**new_globals, **glob}
        methods = methods + meth

    return (code, new_globals, methods, max_thread)

def translate_while(cond, body, globals, max_thread, indent):
    return translate_loop(body, globals, max_thread, indent, cond = translate_expr(cond, globals))

def translate_loop(body, globals, max_thread, indent, cond = '*'):
    (stmts, new_globals, methods, max_thread) = translate_seq(body, globals, max_thread, indent + "  ")
    return (indent + "while (%s) {\n%s%s}\n" % (cond, stmts, indent), new_globals, methods, max_thread)


def translate_if(cond, then_branch, else_branch, globals, max_thread, indent):
    (then_body, then_glob, then_meth, max_thread) = translate_clause(then_branch, globals, max_thread, indent + "  ")
    code = indent + ("if (%s) {\n%s\n%s}\n" % (translate_expr(cond, globals), then_body, indent))
    if else_branch == None:
        else_glob = {}
        else_meth = []
    else:
        (else_body, else_glob, else_meth, max_thread) = translate_clause(else_branch, globals, max_thread, indent + "  ")
        code = code + indent + ("else {\n%s\n%s}\n" % (else_body, indent))
    return (code, {**then_glob, **else_glob}, then_meth + else_meth, max_thread)

def translate_alt(branches, globals, max_thread, indent):
    assert len(branches) > 1, "Conditional should have at least 2 branches"
    (bodies, new_globals, methods, max_thread) = translate_each_clause(branches, globals, max_thread, indent + "  ")
    connective = "%s}\n%selse if (*) {\n" % (indent, indent)
    lastconnective = "%s}\n%selse {\n" % (indent, indent)
    code = indent + "if (*) {\n" + connective.join(bodies[:-1]) + lastconnective + bodies[-1] + indent + "}\n"
    return (code, new_globals, methods, max_thread)

def translate_expr(expr, globals):
    binary_operators = { '<': '<', '<=': '<=', '>': '>', '>=': '>=', '-': '-', '*': '*', '<=>': '<==>', '/=': '!=' }
    nary_infix_operators = { '+': '+', 'and': '&&', 'or': '||', '=>': '==>' }
    if isinstance(expr, list):
        fn, *args = expr
        escaped = escape_id(fn)
        if fn in binary_operators and len(args) == 2:
            lhs = translate_expr(args[0], globals)
            rhs = translate_expr(args[1], globals)
            return "( %s %s %s )" % (lhs, binary_operators[fn], rhs)
        elif fn in nary_infix_operators:
            connective = " " + nary_infix_operators[fn] + " "
            return "( " + connective.join([ translate_expr(x, globals) for x in args ]) + " )"
        elif fn == '-' and len(args) == 1:
            return "( - %s )" % translate_expr(args[0], globals)
        elif fn == '=':
            first = translate_expr(args[0], globals)
            return "( " + " && ".join([ "%s == %s" % (first, translate_expr(x, globals)) for x in args[1:] ]) + " )"
        elif fn == 'not':
            assert len(args) == 1
            return '!' + translate_expr(args[0], globals)
        elif fn == 'select':
            assert len(args) == 2
            return "%s[ %s ]" % (translate_expr(args[0], globals), translate_expr(args[1], globals))
        elif fn == 'store':
            assert len(args) == 3
            array = translate_expr(args[0], globals)
            index = translate_expr(args[1], globals)
            value = translate_expr(args[2], globals)
            return "( %s[ %s := %s ] )" % (array, index, value)
        elif fn == 'if':
            assert len(args) == 3
            cond = translate_expr(args[0], globals)
            then_term = translate_expr(args[1], globals)
            else_term = translate_expr(args[2], globals)
            return '( if %s then %s else %s )' % (cond, then_term, else_term)
        elif escaped in globals:
            (indices, _) = globals[escaped]
            return escaped + "[" + ", ".join([translate_expr(x, globals) for x in args]) + "]"
        else:
            print(globals)
            print(expr)
            raise NotImplementedError("Unknown expression: %s (escaped '%s')" % (fn, escaped))
    elif isinstance(expr, str):
        return escape_id(expr)
    elif isinstance(expr, int):
        return str(expr)
    else:
        raise NotImplementedError("Unknown expression of type %s: %s" % (type(expr), expr))

def escape_id(text):
    reserved_words = ['assert', 'break', 'old']
    if text in reserved_words:
      return 'v_' + text
    return text.replace('-', '_').replace('!', '_')

def print_method(name, body, globals):
    return "procedure %s() returns ()\nmodifies %s;\n{\n%s}\n" % (name, ", ".join(globals.keys()), body)

def print_type(type):
    if isinstance(type, tuple):
        (indices, base) = type
        return "[%s] %s" % (", ".join([print_type(t) for t in indices]), print_type(base))
    elif type == 'Int':
        return 'int'
    elif type == 'Bool':
        return 'bool'
    elif isinstance(type, list) and type[0] == 'Array':
        *indices, base = type[1:]
        return '[%s] %s' % (', '.join([print_type(t) for t in indices]), print_type(base))
    else:
        return type

def print_decl(name, type):
    return "var %s : %s;\n" % (name, print_type(type))

##########################################################################################
# Translate a given weaver example to Boogie.                                               #
##########################################################################################

def read_without_comments(path):
    file = open(path, 'r')
    return "\n".join([ x.split(";",1)[0] for x in file.readlines() ])

def translate_file(path, output):
    sexp = read_without_comments(path)
    parsed = parse_sexps(sexp)

    (stmts, globals, methods) = translate(parsed, 0)
    methods = methods + [('ULTIMATE.start', stmts + "  assert false; // should be unreachable\n")]

    file = open(output, 'w')
    file.write("""/*
* This Boogie code was automatically generated from weaver benchmarks <https://github.com/weaver-verifier/weaver>.
* The original file name was '%s'.
*
* Generated: %s.
*/
""" % (path, datetime.datetime.utcnow().isoformat(timespec='seconds')))
    file.write("".join([ print_decl(name, type) for (name, type) in globals.items() ]))
    file.write("\n\n")
    file.write("\n".join([ print_method(m[0], m[1], globals) for m in methods ]))

if __name__ == '__main__':
    assert len(sys.argv) == 3, "Expects exactly 2 arguments (input and output path)"
    input = sys.argv[1]
    output = sys.argv[2]
    translate_file(input, output)

