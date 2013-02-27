/**
 * Class holding static final objects.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * @author Markus Lindenmann
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
     * Identifier of malloc procedure.
     */
    public static final String MALLOC = "~malloc";
    /**
     * Identifier of free procedure.
     */
    public static final String FREE = "~free";
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
    * Specifies purpose of an auxiliary temporary variable.
    */
   public enum AUXVAR {
	   /**
	    * Auxiliary variable used to get nondeterministically some value.
	    */
	   NONDET("nondet"),
	   
	   /**
	    * Auxiliary variable used to represent the value before a postincrement
	    * or postdecrement. E.g., the <i>t</i> in the sequence of Statements
    	* t:=x;x:=x+1;y:=x+1; which we obtain by translating the statement x++.  
	    */
	   POST_MOD("post"),
	   
	   /**
	    * Auxiliary variable used to store the returned value of a procedure 
	    * call.
	    */
	   RETURNED("ret"),
	   
	   /**
	    * Auxiliary variable used to specify the dimension of an array.
	    */
	   ARRAYDIM("dim"),
	   
	   /**
	    * Auxiliary variable used to initialize array values.
	    */
	   ARRAYINIT("init"),
	   
	   /**
	    * Auxiliary variable used to define a pointer with constant value, 
	    * e.g., (int*) 1048. 
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
	    * Auxiliary variable used to model temporary results of a short-circuit
	    * evaluation, e.g., &&, or ||.
	    */
	   SHORTCIRCUIT("short"),
	   
	   /**
	    * Auxiliary variable used to model temporary results of the ternary 
	    * conditional expression, e.g., (x > 0) ? 23 : 42;
	    */
	   ITE("ite");
	   
	   String m_Id;
	   
	   AUXVAR(String id) {
		   m_Id = id;
	   }
	   
	   /**
	    * @return Identifier used in the variable name.
	    */
	   public String getId() {
		   return m_Id;
	   }
	   
   }


/**
 * Return Variable Declaration for single variable with name tmpName, 
 * InferredType tmpIType at location loc.
 */
public static VariableDeclaration getTempVarVariableDeclaration(
		final String tmpName, final InferredType tmpIType, final ILocation loc) {
	final VarList tempVar;
	if (tmpIType.getType() == Type.Pointer) {
		tempVar = new VarList(loc, new String[] { tmpName },
                MemoryHandler.POINTER_TYPE);
	} else {
        ASTType tempType = new PrimitiveType(loc, tmpIType,
                tmpIType.toString());
		tempVar = new VarList(loc, new String[] { tmpName },
                tempType);
	}
	return new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
};
    	
}
