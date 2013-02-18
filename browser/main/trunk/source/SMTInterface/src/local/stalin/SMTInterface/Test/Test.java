package local.stalin.SMTInterface.Test;

import java.io.InputStreamReader;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.logic.Atom;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.Sort;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;

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
		InputStreamReader in = new InputStreamReader(System.in);
		TermVariable varo = t.createTermVariable("o", refSort);
		TermVariable varT = t.createTermVariable("T", nameSort);
		
		FunctionSymbol nullValue = t.getFunction("null");
		PredicateSymbol isa = t.getPredicate("<:", nameSort, nameSort);
		
		
		FunctionSymbol typeOf = t.createFunction("$typeof", new Sort[] { refSort }, nameSort);
		PredicateSymbol is = t.createPredicate("$Is", new Sort[] { anySort, nameSort});
		FunctionSymbol notnull = t.createFunction("$NotNull", new Sort[] { nameSort }, nameSort);

		int si = SMTInterface.SMTCall(Atom.TRUE, t);
	}

}
