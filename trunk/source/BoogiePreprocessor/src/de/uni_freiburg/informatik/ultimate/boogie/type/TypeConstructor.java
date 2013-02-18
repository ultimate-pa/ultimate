package de.uni_freiburg.informatik.ultimate.boogie.type;

import java.io.Serializable;

public class TypeConstructor implements Serializable{
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 4794962965656111904L;
	private final String name;
	private final boolean isFinite;
	private final int    paramCount;
	private final int[]  paramOrder;
	private final BoogieType synonym;

	public TypeConstructor(String name, boolean isFinite, int paramCount, int[] paramOrder) {
		this(name, isFinite, paramCount, paramOrder, null);
	}
	public TypeConstructor(String name, boolean isFinite, int paramCount, int[] paramOrder, BoogieType synonym) {
		this.name = name;
		this.isFinite = isFinite;
		this.paramCount = paramCount;
		this.paramOrder = paramOrder;
		this.synonym = synonym;
	}
	
	public String getName() {
		return name;
	}
	public int getParamCount() {
		return paramCount;
	}
	public int[] getParamOrder() {
		return paramOrder;
	}
	public BoogieType getSynonym() {
		return synonym;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(name);
		if (paramOrder.length > 0) {
			sb.append('<');
			String comma = "";
			for (int i = 0; i < paramOrder.length; i++) {
				sb.append(comma).append(paramOrder[i]);
				comma = ",";
			}
			sb.append('>');
		}
		if (synonym != null)
			sb.append('=').append(synonym);
		return sb.toString();
	}
	
	public boolean isFinite() {
		return isFinite;
	}
}
