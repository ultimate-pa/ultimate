/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * Class holding static final objects.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Markus Lindenmann
 * @author Matthias Heizmann
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @date 16.08.2012
 */
public final class SFO {

	/**
	 * String representing the result variable in Boogie.
	 */
	public static final String RES = "#res";
	/**
	 * String holding "int".
	 */
	public static final String INT = "int";
	/**
	 * String holding "unknown"
	 */
	public static final String UNKNOWN = "unknown";
	/**
	 * String holding "string".
	 */
	public static final String STRING = "string";
	/**
	 * String holding "bool".
	 */
	public static final String BOOL = "bool";
	/**
	 * String holding "real".
	 */
	public static final String REAL = "real";
	/**
	 * Temp variable name.
	 */
	public static final String TEMP = "#t~";
	/**
	 * In Param Prefix.
	 */
	public static final String IN_PARAM = "#in~";
	/**
	 * String holding "1".
	 */
	public static final String NR1 = "1";
	/**
	 * String holding "0".
	 */
	public static final String NR0 = "0";
	/**
	 * String holding "ULTIMATE.init".
	 */
	public static final String INIT = "ULTIMATE.init";
	/**
	 * String holding "ULTIMATE.start".
	 */
	public static final String START = "ULTIMATE.start";
	/**
	 * The empty String.
	 */
	public static final String EMPTY = "";
	/**
	 * Prefix for variables, not contained in the C code.
	 */
	public static final String NO_REAL_C_VAR = "NO_REAL_C_VAR";
	/**
	 * Prefix for unnamed in parameters.
	 */
	public static final String UNNAMED = "unnamed~";
	/**
	 * String holding "0.0".
	 */
	public static final String NR0F = "0.0";

	/**
	 * Identifier of free procedure.
	 */
	public static final String FREE = "ULTIMATE.free";
	/**
	 * Identifier of free procedure.
	 */
	public static final String DEALLOC = "ULTIMATE.dealloc";
	/**
	 * The "#length" array identifier.
	 */
	public static final String LENGTH = "#length";
	/**
	 * The "#valid" array identifier.
	 */
	public static final String VALID = "#valid";
	/**
	 * The "#memory" array identifier.
	 */
	public static final String MEMORY = "#memory";
	/**
	 * The "$Pointer$" type identifier.
	 */
	public static final String POINTER = "$Pointer$";
	/**
	 * The "offset" field of the pointer type.
	 */
	public static final String POINTER_OFFSET = "offset";
	/**
	 * The "base" field of the pointer type.
	 */
	public static final String POINTER_BASE = "base";
	/**
	 * Sizeof constant prefix "#sizeof~".
	 */
	public static final String SIZEOF = "#sizeof~";
	/**
	 * Offset constant prefix "#offset~".
	 */
	public static final String OFFSET = "#offset~";
	/**
	 * Identifier for the sizeof-pointer-constant.
	 */
	public static final String SIZEOF_POINTER_ID = SFO.SIZEOF + SFO.POINTER;
	/**
	 * Identifier of the null pointer.
	 */
	public static final String NULL = "#NULL";
	/**
	 * Identifier for function pointers.
	 */
	public static final String FUNCTION_ADDRESS = "#funAddr~";
	/**
	 * Loop (entry/exit) labels are built with this.
	 */
	public static final String LOOPLABEL = "Loop~";
	/**
	 * Prefix for all auxiliary functions that we add to the Boogie program, e.g., bitwise and will be ~bvand.
	 */
	public static final String AUXILIARY_FUNCTION_PREFIX = "~";

	/**
	 * combined SFOs for memory arrays:
	 */
//	public static final String MEMORY_INT = MEMORY + "_" + INT;
	public static final String MEMORY_REAL = MEMORY + "_" + REAL;
	public static final String MEMORY_POINTER = MEMORY + "_" + POINTER;

	public static final String MEMCPY_DEST = "dest";
	public static final String MEMCPY_SRC = "src";
	public static final String MEMCPY_SIZE = "size";
	public static final String MEMCPY = "#memcpy";

	public static final String STRCPY_DEST = "dest";
	public static final String STRCPY_SRC = "src";

	public static final String TO_INT = "#to_int";
	public static final String MEMSET = "ULTIMATE.memset";

	/**
	 * name of C's "main" procedure
	 */
	public static final String MAIN = "main";

	/**
	 * Name of the memory allocation procedure used by the memory model.
	 */
	public static final String ALLOC = "#Ultimate.alloc";

	public static final String C_MEMCPY = "#Ultimate.C_memcpy";

	public static final String C_MEMMOVE = "#Ultimate.C_memmove";

	public static final String C_MEMSET = "#Ultimate.C_memset";

	public static final String C_STRCPY = "#Ultimate.C_strcpy";

	public static final String ULTIMATE_PTHREADS_MUTEX = "#pthreadsMutex";


	/**
	 * Specifies purpose of an auxiliary temporary variable.
	 */
	public enum AUXVAR {
		/**
		 * variable used for a loop that we introduce through the translation
		 */
		LOOPCTR("loopctr"),

		/**
		 * variable used for an increasing address offset in a loop that we introduce through the translation
		 */
		OFFSET("offset"),


		/**
		 * Auxiliary variable used to store the result of a call of a function pointer.
		 */
		FUNCPTRRES("funptrres"),

		/**
		 * Auxiliary variable used to get some value nondeterministically.
		 */
		NONDET("nondet"),

		/**
		 * Auxiliary variable used to represent the value after a prefix increment or prefix decrement (e.g.,
		 * <code>++x</code>).
		 */
		PRE_MOD("pre"),

		/**
		 * Auxiliary variable used to represent the value before a postfix increment or postfix decrement (e.g.,
		 * <code>x++</code>).
		 */
		POST_MOD("post"),

		/**
		 * Auxiliary variable used to store the returned value of a procedure call.
		 */
		RETURNED("ret"),

		/**
		 * Auxiliary variable used to specify the dimension of an array.
		 */
		ARRAYDIM("dim"),

		/**
		 * Auxiliary variable used to initialize array values.
		 */
		ARRAYINIT("arrayinit"),

		/**
		 * Auxiliary variable used as iterator variable for loops that initializer array values.
		 */
		ARRAYINITITERATOR("iter"),

		/**
		 * Auxiliary variable used for a helper array (serves the same purpose as a struct constructor when a whole
		 * array is copied.
		 */
		ARRAYCOPY("arrayCopy"),

		/**
		 * Auxiliary variable used to define a pointer with constant value, e.g., (int*) 1048.
		 */
		CONSTPOINTER("const"),

		/**
		 * Auxiliary variable used to model the result of a malloc call.
		 */
		MALLOC("malloc"),

		/**
		 * Auxiliary variable used to store the result of a memory access.
		 */
		MEMREAD("mem"),

		/**
		 * Auxiliary variable used to model temporary results of a short-circuit evaluation, e.g., &&, or ||.
		 */
		SHORTCIRCUIT("short"),

		/**
		 * Auxiliary variable used to model temporary results of the ternary conditional expression, e.g., (x > 0) ? 23
		 * : 42;
		 */
		ITE("ite"),

		/**
		 * Auxiliary variable used for arrow operator (field access of dereferenced pointer.
		 */
		ARROW("arrow"),

		/**
		 * Auxiliary variable used for union initialisation.
		 */
		UNION("union"),

		/**
		 * Auxiliary variable used for the memory address of a string literal
		 */
		STRINGLITERAL("string"),

		/**
		 * Auxiliary variable used for struct initialisation.
		 */
		STRUCTINIT("structinit"),

		/**
		 *
		 */
		SWITCH("switch"),

		/**
		 * Auxiliary variable used for the result of a call to the 'builtin' memcpy function
		 */
		MEMCPYRES("memcpy~res"),

		/**
		 * Auxiliary variable used for the result of a call to the 'builtin' memmove function
		 */
		MEMMOVERES("memmove~res"),

		/**
		 * Auxiliary variable used for the result of a call to the 'builtin' memset function
		 */
		MEMSETRES("memset~res"),

		/**
		 * Auxiliary variable used for the result of a call to the 'builtin' memset function
		 */
		STRCPYRES("strcpy~res"),


		/**
		 * Name for dummy expressions that represent a "void" result. Those identifier expressions may not be used
		 * anywhere and thus should get an error BoogieType.
		 * (note that this string has to fit the regex that is checked during creation of an IdentifierExpression...)
		 */
		DUMMY_VOID("#dummy~void~value"),

		;


		private final String mId;

		AUXVAR(final String id) {
			mId = id;
		}

		/**
		 * @return Identifier used in the variable name.
		 */
		public String getId() {
			return mId;
		}

	}

	/**
	 * Return Variable Declaration for single variable with name tmpName, InferredType tmpIType at location loc.
	 */
	public static VariableDeclaration getTempVarVariableDeclaration(final String tmpName, final ASTType astType,
			final ILocation loc) {
		final VarList tempVar = new VarList(loc, new String[] { tmpName }, astType);
		return new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
	}

	/**
	 * Build the name of a Boogie function for a given SMT-LIB function name and a C type. Since SMT-LIB allows
	 * overloading of functions but Boogie does not, we have to construct unique identifiers. We do this by appending
	 * the C type. By convention we use an additional prefix for each such function. This should avoid that we have name
	 * clashes with functions that occur in the C program.
	 *
	 * @param smtFunctionName
	 *            The name of the conversion symbol.
	 * @param type
	 *            The type of the conversion.
	 * @return an identifier for a Boogie function that represents some SMT function symbol used for converting or
	 *         creating constants.
	 */
	public static String getBoogieFunctionName(final String smtFunctionName, final CPrimitive type) {
		return getBoogieFunctionName(smtFunctionName, type.toString());
	}

	private static String getBoogieFunctionName(final String smtFunctionName, final String suffix) {
		final String escapedSmtFunctionName = smtFunctionName.replace("+", "Plus").replace("-", "Minus");
		return SFO.AUXILIARY_FUNCTION_PREFIX + escapedSmtFunctionName + SFO.AUXILIARY_FUNCTION_PREFIX + suffix;
	}

	public static Pair<String, CPrimitives> reverseBoogieFunctionName(final String functionName) {
		if (functionName == null) {
			return null;
		}
		final String[] splitted = functionName.split(SFO.AUXILIARY_FUNCTION_PREFIX);
		if (splitted.length < 3) {
			return null;
		}
		final String smtFunctionName = splitted[1];
		final CPrimitives prim = Enum.valueOf(CPrimitives.class, splitted[2]);
		return new Pair<>(smtFunctionName, prim);
	}

}
