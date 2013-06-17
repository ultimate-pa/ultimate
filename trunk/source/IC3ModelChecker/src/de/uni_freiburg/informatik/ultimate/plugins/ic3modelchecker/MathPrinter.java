package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/** Converts a given term into String representation, using mathematica syntax. */
public class MathPrinter {
	private static HashMap<String, String> functionEquiv;
	private static HashMap<String, String> infixNotated;
	
	public static void init() {
		// TODO: Make theory-independent?
		functionEquiv = new HashMap<String, String>();
		functionEquiv.put("and", "And");
		functionEquiv.put("or", "Or");
		functionEquiv.put("xor", "Xor");
		functionEquiv.put("=>", "Implies");
		functionEquiv.put("!", "Not");
		functionEquiv.put("not", "Not");
		functionEquiv.put("ite", "If");
		functionEquiv.put("true", "True");
		functionEquiv.put("false", "False");
		
		infixNotated = new HashMap<String, String>();
		infixNotated.put("+", "+");
		infixNotated.put("-", "-");
		infixNotated.put("*", "*");
		infixNotated.put("/", "/");
		infixNotated.put("=", "==");
		infixNotated.put("<=", "<=");
		infixNotated.put(">=", ">=");
		infixNotated.put(">", ">");
		infixNotated.put("<", "<");
	}

	public static String convert(Term originalTerm) {
		HashMap<Term, String> converted = new HashMap<Term, String>();
		ArrayDeque<Term> todo = new ArrayDeque<Term>();
		todo.push(originalTerm);
		
		while (!todo.isEmpty()) {
			Term term = todo.peek();
			String string = converted.get(term);
			if (string == null) {
				resolve(term, converted, todo);
			} else {
				todo.pop();
			}
		}
		String result = converted.get(originalTerm);
		assert(result != null);
		return result;
	}
	
	/** Either composes term if subelements are all found in converted and puts it
	 * into converted, or pushes missing subelements onto todo stack. */
	private static void resolve(Term term, HashMap<Term, String> converted, ArrayDeque<Term> todo) {
		//TreeIC3.logger().debug("MathPrinter: Resolve "+term.toStringDirect());
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol function = appTerm.getFunction();
			Term[] params = appTerm.getParameters();
			ArrayList<String> paramsAsStrings = getConvertedParams(params, converted, todo);
			if (paramsAsStrings != null) {
				//TreeIC3.logger().debug("MathPrinter: Found all converted params, compose it");
				composeTerm(function, paramsAsStrings, term, converted);
			}
		} else if (term instanceof ConstantTerm) {
			ConstantTerm constantTerm = (ConstantTerm) term;
			Object value = constantTerm.getValue();
			if (value instanceof BigDecimal) {
				converted.put(term, bigDecimalToCommaFreeString((BigDecimal) value));
			} else {
				String string = term.toStringDirect();
				converted.put(term, string);
			}
		} else {
			String string = term.toStringDirect();
			converted.put(term, string);
			//TreeIC3.logger().debug("MathPrinter: Converted "+string);
		}
	}
	
	/** Retrieves all conversion results for all given params, or null if at least one param could not be resolved.
	 * All params that could not be resolved are pushed onto the todo stack. */
	private static ArrayList<String> getConvertedParams(Term[] params, HashMap<Term, String> converted, ArrayDeque<Term> todo) {
		ArrayList<String> result = new ArrayList<String>();
		boolean foundAll = true;
		for (Term term : params) {
			String string = converted.get(term);
			if (string == null) {
				foundAll = false;
				todo.push(term);
				//TreeIC3.logger().debug("MathPrinter: Push param "+term.toStringDirect());
			} else if (foundAll == true) {
				result.add(string);
			}
		}
		if (foundAll) return result;
		else return null;
	}
	
	private static void composeTerm(FunctionSymbol function, ArrayList<String> paramsAsStrings, 
	 Term term, HashMap<Term, String> converted) {
		StringBuilder builder = new StringBuilder();
		String functionName = function.getName();
		String mathEquiv = functionEquiv.get(functionName);
		String infixEquiv = infixNotated.get(functionName);
		if (functionName.equals("-") && paramsAsStrings.size() == 1) {
			// Special case: If we have a minus with a single parameter,
			// it won't be treated properly below by infixEquiv.
			// So we deal with it here.
			builder.append("(- ");
			builder.append(paramsAsStrings.get(0));
			builder.append(")");
			//TreeIC3.logger().debug("Composed result: "+builder.toString());
			converted.put(term, builder.toString());
		} else if (mathEquiv != null) {
			builder.append(mathEquiv);
			if (paramsAsStrings.size() > 0) {
				builder.append("[");
				appendAll(builder, ", ", paramsAsStrings);
				builder.append("]");
			}
			//TreeIC3.logger().debug("Composed result: "+builder.toString());
			converted.put(term, builder.toString());
		} else if (infixEquiv != null) {
			builder.append("(");
			appendAll(builder, " "+infixEquiv+" ", paramsAsStrings);
			builder.append(")");
			//TreeIC3.logger().debug("Composed result: "+builder.toString());
			converted.put(term, builder.toString());
		} else {
			throw new RuntimeException("MathPrinter: Couldn't compose, unhandled function symbol!");
		}
	}
	
	private static void appendAll(StringBuilder builder, String separator, ArrayList<String> params) {
		assert(params.size() > 0);
		builder.append(params.get(0));
		for (int i = 1; i < params.size(); i++) {
			builder.append(separator);
			builder.append(params.get(i));
		}
	}

	public static String createExistPrefix(Set<TermVariable> vars) {
		StringBuilder builder = new StringBuilder();
		builder.append("Exists[{");
		Iterator<TermVariable> iterator = vars.iterator();
		while (iterator.hasNext()) {
			builder.append(iterator.next().getName());
			if (iterator.hasNext())
				builder.append(", ");
		}
		builder.append("}, ");
		return builder.toString();
	}
	
	private static String bigDecimalToCommaFreeString(BigDecimal bigDecimal) {
		BigInteger unscaled = bigDecimal.unscaledValue();
		int scale = bigDecimal.scale();
		if (scale <= 0)
			return bigDecimal.toPlainString();
		else
			return ("("+unscaled+" / "+BigInteger.TEN.pow(scale)+")");
	}
}
