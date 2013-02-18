package de.uni_freiburg.informatik.ultimate.boogie.type;

/**
 * A function signature.  It consists of a number of type arguments, parameters each 
 * with a type and optionally a name and a result value type.
 * 
 * An example of a function signature is 
 * <pre>&lt;x&gt;(field: name x, heap: &lt;y&gt;[ref, name y]y, ref)x</pre>
 *  
 * @author hoenicke
 *
 */
public class FunctionSignature {
	/**
	 * Number of type arguments (placeholder).
	 */
	private final int          typeArgCount;
	/**
	 * Names of the parameters, an entry is null if not given.
	 * The length must be equal to paramTypes.length.
	 */
	private final String[]     paramNames;
	/**
	 * Name of the result parameter.
	 */
	private final String       resultName;
	/**
	 * Types of the parameters.
	 */
	private final BoogieType[] paramTypes;
	/**
	 * Type of the result.
	 */
	private final BoogieType   resultType;
	
	public FunctionSignature(int typeArgCount, String[] paramNames,
			BoogieType[] paramTypes, String resultName, BoogieType resultType) {
		super();
		this.typeArgCount = typeArgCount;
		this.paramNames = paramNames;
		this.paramTypes = paramTypes;
		this.resultName = resultName;
		this.resultType = resultType;
	}

	/**
	 * @return the number of type arguments (placeholders).
	 */
	public int getTypeArgCount() {
		return typeArgCount;
	}

	/**
	 * @return the number of parameters.
	 */
	public int getParamCount() {
		return paramTypes.length;
	}

	/**
	 * @param i the position of the parameter.
	 * @return the name of the ith parameter.
	 */
	public String getParamName(int i) {
		return paramNames[i];
	}

	/**
	 * @param i the position of the parameter.
	 * @return the type of the ith parameter.
	 */
	public BoogieType getParamType(int i) {
		return paramTypes[i];
	}

	/**
	 * @return the type of the result.
	 */
	public BoogieType getResultType() {
		return resultType;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		String delim;
		if (typeArgCount > 0) {
			sb.append("<");
			delim ="";
			for (int i = 0; i < typeArgCount; i++) {
				sb.append(delim).append("$"+i);
				delim = ",";
			}
			sb.append(">");
		}
		sb.append("(");
		delim = "";
		for (int i = 0; i < paramTypes.length; i++) {
			sb.append(delim);
			if (paramNames[i] != null)
				sb.append(paramNames[i]).append(":");
			sb.append(paramTypes[i].toString(typeArgCount, false));
			delim = ", ";
		}
		sb.append(") returns (");
		if (resultName != null)
			sb.append(resultName).append(":");
		sb.append(resultType.toString(typeArgCount, false));
		sb.append(")");
		return sb.toString();
	}
}
