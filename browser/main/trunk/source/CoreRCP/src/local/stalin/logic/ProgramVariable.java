package local.stalin.logic;

/**
 * Represents a program variable.  From the logical point of view a program variable
 * is a set of constant symbols, one for each program computation step.  These are
 * distinguished from the logical variables (TermVariable), which are used in 
 * quantifiers and let formulas.
 * 
 * A program variable has a name and a sort.
 * @author hoenicke
 *
 */
public class ProgramVariable {
	private final String name;
	private final Sort sort;
	
	public ProgramVariable(String n, Sort s) {
		name = n;
		sort = s;
	}
	
	public String getName() {
		return name;
	}
	
	public Sort getSort() {
		return sort;
	}

	public String toString() {
		return "(_v"+name+" "+sort+")";
	}
}
