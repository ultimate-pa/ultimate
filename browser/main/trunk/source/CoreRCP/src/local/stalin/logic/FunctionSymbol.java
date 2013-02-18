package local.stalin.logic;

import java.io.Serializable;

/**
 * Represents a function symbol.  Each function symbol has a name, a sort and
 * zero or more parameter sorts.  A constant symbol is represented as a function 
 * symbols with zero parameters.
 * @author hoenicke
 *
 */
public class FunctionSymbol implements Serializable {
	private static final long serialVersionUID = -2928710994807286022L;
	private final String name;
	private final Sort[] paramSort;
	private final Sort returnSort;
	private final boolean isIntern;
	
	FunctionSymbol(String n, Sort[] params, Sort result) {
		this (n, params, result, false);
	}
	
	FunctionSymbol(String n, Sort[] params, Sort result, boolean intern) {
		name = n;
		paramSort = params;
		returnSort = result;
		this.isIntern = intern;
	}
	
	public String getName() {
		return name;
	}
	
	public boolean isIntern() {
		return isIntern;
	}
	
	public int getParameterCount() {
		return paramSort.length;
	}
	
	public Sort getParameterSort(int i) {
		return paramSort[i];
	}
	
	public Sort getReturnSort() {
		return returnSort;
	}
	
	Sort[] getParameterSorts() {
		return paramSort;
	}

	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("(").append(name);
		for (Sort s : paramSort) {
			sb.append(" ").append(s);
		}
		sb.append(" ").append(returnSort);
		sb.append(")");
		return sb.toString();
	}
}
