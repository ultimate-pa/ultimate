/*
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.logic;

/**
 * This interface contains the names of all SMTLIB functions, attributes, and values.
 *
 * @author Jochen Hoenicke
 */
public interface SMTLIBConstants {
	// Base Theory
	public static final String BOOL = "Bool";
	public static final String NOT = "not";
	public static final String AND = "and";
	public static final String OR = "or";
	public static final String IMPLIES = "=>";
	public static final String EQUALS = "=";
	public static final String DISTINCT = "distinct";
	public static final String XOR = "xor";
	public static final String ITE = "ite";
	public static final String TRUE = "true";
	public static final String FALSE = "false";
	public static final String FUNC = "->";

	// Arithmetic
	public static final String INT = "Int";
	public static final String REAL = "Real";
	public static final String PLUS = "+";
	public static final String MINUS = "-";
	public static final String MUL = "*";
	public static final String DIVIDE = "/";
	public static final String DIV = "div";
	public static final String MOD = "mod";
	public static final String DIVISIBLE = "divisible";
	public static final String ABS = "abs";
	public static final String GT = ">";
	public static final String GEQ = ">=";
	public static final String LT = "<";
	public static final String LEQ = "<=";
	public static final String TO_REAL = "to_real";
	public static final String TO_INT = "to_int";
	public static final String IS_INT = "is_int";

	// Arrays
	public static final String ARRAY = "Array";
	public static final String STORE = "store";
	public static final String SELECT = "select";
	public static final String CONST = "const";
	public static final String ARRAYOF = ".arrayof";

	// Datatypes
	public static final String IS = "is";

	// Bitvector
	public static final String BITVEC = "BitVec";
	public static final String CONCAT = "concat";
	public static final String EXTRACT = "extract";
	public static final String BVNOT = "bvnot";
	public static final String BVAND = "bvand";
	public static final String BVOR = "bvor";
	public static final String BVNEG = "bvneg";
	public static final String BVADD = "bvadd";
	public static final String BVMUL = "bvmul";
	public static final String BVUDIV = "bvudiv";
	public static final String BVUREM = "bvurem";
	public static final String BVSHL = "bvshl";
	public static final String BVLSHR = "bvlshr";
	public static final String BVNAND = "bvnand";
	public static final String BVNOR = "bvnor";
	public static final String BVXOR = "bvxor";
	public static final String BVXNOR = "bvxnor";
	public static final String BVCOMP = "bvcomp";
	public static final String BVSUB = "bvsub";
	public static final String BVSDIV = "bvsdiv";
	public static final String BVSREM = "bvsrem";
	public static final String BVSMOD = "bvsmod";
	public static final String BVASHR = "bvashr";
	public static final String REPEAT = "repeat";
	public static final String ZERO_EXTEND = "zero_extend";
	public static final String SIGN_EXTEND = "sign_extend";
	public static final String ROTATE_LEFT = "rotate_left";
	public static final String ROTATE_RIGHT = "rotate_right";
	public static final String BVULT = "bvult";
	public static final String BVULE = "bvule";
	public static final String BVUGT = "bvugt";
	public static final String BVUGE = "bvuge";
	public static final String BVSLT = "bvslt";
	public static final String BVSLE = "bvsle";
	public static final String BVSGT = "bvsgt";
	public static final String BVSGE = "bvsge";
	public static final String PREFIX_BINARY = "#b";
	public static final String PREFIX_HEX = "#x";

	// Floating Point
	public static final String FLOATINGPOINT = "FloatingPoint";
	public static final String ROUNDINGMODE = "RoundingMode";
	public static final String FP = "fp";
	public static final String TO_FP = "to_fp";
	public static final String TO_FP_UNSIGNED = "to_fp_unsigned";
	public static final String FP_TO_UBV = "fp.to_ubv";
	public static final String FP_TO_SBV = "fp.to_sbv";
	public static final String FP_INFINITY = "+oo";
	public static final String FP_NEG_INFINITY = "-oo";
	public static final String FP_ZERO = "+zero";
	public static final String FP_NEG_ZERO = "-zero";
	public static final String FP_NAN = "NaN";
	public static final String FLOAT16 = "Float16";
	public static final String FLOAT32 = "Float32";
	public static final String FLOAT64 = "Float64";
	public static final String FLOAT128 = "Float128";
	public static final String ROUND_NEAREST_TIES_TO_EVEN = "roundNearestTiesToEven";
	public static final String ROUND_NEAREST_TIES_TO_AWAY = "roundNearestTiesToAway";
	public static final String ROUND_TOWARDS_POSITIVE = "roundTowardsPositive";
	public static final String ROUND_TOWARDS_NEGATIVE = "roundTowardsNegative";
	public static final String ROUND_TOWARDS_ZERO = "roundTowardsZero";
	public static final String FP_ABS = "fp.abs";
	public static final String FP_NEG = "fp.neg";
	public static final String FP_MIN = "fp.min";
	public static final String FP_MAX = "fp.max";
	public static final String FP_REM = "fp.rem";
	public static final String FP_ADD = "fp.add";
	public static final String FP_SUB = "fp.sub";
	public static final String FP_MUL = "fp.mul";
	public static final String FP_DIV = "fp.div";
	public static final String FP_FMA = "fp.fma";
	public static final String FP_SQRT = "fp.sqrt";
	public static final String FP_ROUND_TO_INTEGRAL = "fp.roundToIntegral";
	public static final String FP_LEQ = "fp.leq";
	public static final String FP_LT = "fp.lt";
	public static final String FP_GEQ = "fp.geq";
	public static final String FP_GT = "fp.gt";
	public static final String FP_EQ = "fp.eq";
	public static final String FP_IS_NORMAL = "fp.isNormal";
	public static final String FP_IS_SUBNORMAL = "fp.isSubnormal";
	public static final String FP_IS_ZERO = "fp.isZero";
	public static final String FP_IS_INFINITE = "fp.isInfinite";
	public static final String FP_IS_NAN = "fp.isNaN";
	public static final String FP_IS_NEGATIVE = "fp.isNegative";
	public static final String FP_IS_POSITIVE = "fp.isPositive";
	public static final String FP_TO_REAL = "fp.to_real";

	// Strings
	public static final String STRING = "String";
	public static final String REGLAN = "RegLan";

	public static final String CHAR = "char";

	public static final String STR_CONCAT = "str.++";
	public static final String STR_LEN = "str.len";
	public static final String STR_LT = "str.<";
	public static final String STR_TO_RE = "str.to_re";
	public static final String STR_IN_RE = "str.in_re";
	public static final String RE_NONE = "re.none";
	public static final String RE_ALL = "re.all";
	public static final String RE_ALLCHAR = "re.allchar";
	public static final String RE_CONCAT = "re.++";
	public static final String RE_UNION = "re.union";
	public static final String RE_INTER = "re.inter";
	public static final String RE_STAR = "re.*";

	public static final String STR_LE = "str.<=";
	public static final String STR_AT = "str.at";
	public static final String STR_SUBSTR = "str.substr";
	public static final String STR_PREFIXOF = "str.prefixof";
	public static final String STR_SUFFIXOF = "str.suffixof";
	public static final String STR_CONTAINS = "str.contains";
	public static final String STR_INDEXOF = "str.indexof";
	public static final String STR_REPLACE = "str.replace";
	public static final String STR_REPLACE_ALL = "str.replace_all";
	public static final String STR_REPLACE_RE = "str.replace_re";
	public static final String STR_REPLACE_RE_ALL = "str.replace_re_all";
	/** Regex complement */
	public static final String RE_COMP = "re.comp";
	/** Regex difference */
	public static final String RE_DIFF = "re.diff";
	public static final String RE_PLUS = "re.+";
	/** RegEx option: (re_opt re) = (re.union (re.to_str "") re) */
	public static final String RE_OPT = "re.opt";
	public static final String RE_RANGE = "re.range";
	public static final String RE_ITER = "re.^";
	public static final String RE_LOOP = "re.loop";

	public static final String STR_IS_DIGIT = "str.is_digit";
	public static final String STR_TO_CODE = "str.to_code";
	public static final String STR_FROM_CODE = "str.from_code";
	public static final String STR_TO_INT = "str.to_int";
	public static final String STR_FROM_INT = "str.from_int";

	// official attributes
	public static final String NAMED = ":named";
	public static final String PATTERN = ":pattern";

	// command reply
	public String ERROR = "error";
	public String UNSUPPORTED = "unsupported";
	public String SUCCESS = "success";
	public String SAT = "sat";
	public String UNKNOWN = "unknown";
	public String UNSAT = "unsat";

	// info keys and their values
	public String SMT_LIB_VERSION = ":smt-lib-version";
	public String ERROR_BEHAVIOR = ":error-behavior";
	public String CONTINUED_EXECUTION = "continued-execution";
	public String IMMEDIATE_EXIT = "immediate-exit";
	public String NAME = ":name";
	public String VERSION = ":version";
	public String AUTHORS = ":authors";
	public String STATUS = ":status";
	public String ALL_STATISTICS = ":all-statistics";
	public String REASON_UNKNOWN = ":reason-unknown";
	public String ASSERTION_STACK_LEVELS = ":assertion-stack-levels";

	// option keys and their values
	public String DIAGNOSTIC_OUTPUT_CHANNEL = ":diagnostic-output-channel";
	public String GLOBAL_DECLARATIONS = ":global-declarations";
	public String INTERACTIVE_MODE = ":interactive-mode";
	public String PRINT_SUCCESS = ":print-success";
	public String PRODUCE_ASSERTIONS = ":produce-assertions";
	public String PRODUCE_ASSIGNMENTS = ":produce-assignments";
	public String PRODUCE_MODELS = ":produce-models";
	public String PRODUCE_PROOFS = ":produce-proofs";
	public String PRODUCE_UNSAT_ASSUMPTIONS = ":produce-unsat-assumptions";
	public String PRODUCE_UNSAT_CORES = ":produce-unsat-cores";
	public String RANDOM_SEED = ":random-seed";
	public String REGULAR_OUTPUT_CHANNEL = ":regular-output-channel";
	public String REPRODUCIBLE_RESOURCE_LIMITS = ":reproducable-resource-limits";
	public String VERBOSITY = ":verbosity";
	public String STDOUT = "stdout";
	public String STDERR = "stderr";
}
