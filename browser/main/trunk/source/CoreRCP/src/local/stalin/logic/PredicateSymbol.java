package local.stalin.logic;

import java.io.Serializable;


/**
 * Represents a function symbol.  Each predicate symbol has a name and
 * zero or more parameter sorts.
 * @author hoenicke
 *
 */
public class PredicateSymbol implements Serializable {
	private static final long serialVersionUID = 8532130513846734720L;
	private final String name;
	private final Sort[] paramSort;
	private final boolean isIntern;
	
	/**
	 * The constructor.  Don't call this; use Theory.createPredicate instead!
	 * @param name
	 * @param paramSort
	 */
	PredicateSymbol(String name, Sort[] paramSort) {
		this (name, paramSort, false);
	}
	
	PredicateSymbol(String name, Sort[] paramSort, boolean isIntern) {
		this.name = name;
		this.paramSort = paramSort;
		this.isIntern = isIntern;
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
	
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("(").append(name);
		for (Sort s : paramSort) {
			sb.append(" ").append(s);
		}
		sb.append(")");
		return sb.toString();
	}
	Sort[] getParameterSorts() {
		return paramSort;
	}
}
