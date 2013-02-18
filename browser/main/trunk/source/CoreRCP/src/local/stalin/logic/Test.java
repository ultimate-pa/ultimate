package local.stalin.logic;

import java.io.PrintWriter;

public class Test {

	/**
	 * Test class that creates some formulas in a theory.
	 * Note that the axioms are unsatisfiable (they come from the BoogiePL technical report).
	 */
	@SuppressWarnings("unused")
	public static void main(String[] args) {
		Theory t = new Theory();
		Sort intSort = t.getSort("Int");
		Sort anySort = t.createSort("any");
		Sort refSort = t.createSort("ref");
		Sort nameSort = t.createSort("name");
		TermVariable varo = new TermVariable("o", refSort);
		TermVariable varT = new TermVariable("T", nameSort);
		
		FunctionSymbol nullValue = t.getFunction("null");
		PredicateSymbol isa = t.getPredicate("<:", nameSort, nameSort);
		
		
		FunctionSymbol typeOf = t.createFunction("$typeof", new Sort[] { refSort }, nameSort);
		PredicateSymbol is = t.createPredicate("$Is", new Sort[] { anySort, nameSort});
		FunctionSymbol notnull = t.createFunction("$NotNull", new Sort[] { nameSort }, nameSort);

		PrintWriter pw = new PrintWriter(System.out);
		t.dumpBenchmark(pw, Atom.TRUE);
		pw.flush();
	}

}
