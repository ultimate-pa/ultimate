package local.stalin.logic;

import java.io.Serializable;

public class FormulaVariable implements Serializable {
	private static final long serialVersionUID = -744317136918002969L;
	private String name;
	
	/**
	 * @return the name of the formula variable.
	 */
	public String getName() {
		return name;
	}
	
	public String toString() {
		return "$"+name;
	}

	FormulaVariable(String name) {
		this.name = name;
	}
}
