package local.stalin.logic;

import java.io.Serializable;

public class Sort implements Serializable {
	private static final long serialVersionUID = -6969656028070243975L;
	String name;
	boolean isIntern;
	
	/*
	 * If this is an array sort, it contains the functions to select and store elements.
	 */
//	FunctionSymbol select;
//	FunctionSymbol store;
	
	Sort(String n, boolean intern) {
		name = n;
		isIntern = intern;
	}
	
	public String getName() {
		return name;
	}
	
	public boolean isIntern() {
		return isIntern;
	}
	
	public String toString() {
		return name;
	}
}
