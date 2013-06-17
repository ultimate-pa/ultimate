package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class TreeSizeCalculator {
	public static Integer calcTreeSize(Term originalTerm, HashMap<Term, Integer> convertedCache) {
		if (convertedCache == null)
			convertedCache = new HashMap<Term, Integer>();
		if (convertedCache.containsKey(originalTerm))
			return convertedCache.get(originalTerm);
		ArrayDeque<Term> todo = new ArrayDeque<Term>();
		
		todo.push(originalTerm);
		
		while (!todo.isEmpty()) {
			Term term = todo.peek();
			Integer treeSize = convertedCache.get(term);
			if (treeSize == null) {
				resolve(term, convertedCache, todo);
			} else {
				todo.pop();
			}
		}
		Integer result = convertedCache.get(originalTerm);
		assert(result != null);
		return result;
	}
	
	/** Either composes term if subelements are all found in converted and puts it
	 * into convertedCache, or pushes missing subelements onto todo stack. */
	private static void resolve(Term term, HashMap<Term, Integer> converted, ArrayDeque<Term> todo) {
		Theory theory = term.getTheory();
		if (term instanceof TermVariable) {
			converted.put(term, 0);
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol function = appTerm.getFunction();
			String functionName = function.getName();
			Term[] params = appTerm.getParameters();
			ArrayList<Integer> convertedParamSizes = getConvertedParamSizes(params, converted, todo);
			if (convertedParamSizes != null) {
				if (appTerm.equals(theory.TRUE) || appTerm.equals(theory.FALSE)) {
					converted.put(appTerm, 0);
				} else if (functionName.equals("not") || functionName.equals("and") || functionName.equals("or")
							|| functionName.equals("xor") || functionName.equals("=>")
							|| (functionName.equals("=") && function.getParameterSort(0) == theory.getBooleanSort())
							|| (functionName.equals("distinct") && function.getParameterSort(0) == theory.getBooleanSort())) {
					int sum = params.length-1;
					for (Integer convertedParamSize : convertedParamSizes) {
						sum += convertedParamSize;
					}
					converted.put(appTerm, sum);
				} else if (functionName.equals("ite")) {
					int sum = 1;
					for (Integer convertedParamSize : convertedParamSizes) {
						sum += convertedParamSize;
					}
					converted.put(appTerm, sum);
				} else {
					converted.put(term, 0);
				}
			}
		} else if (term instanceof LetTerm) {
			throw new RuntimeException("Cannot handle LetTerm!");
		} else {
			converted.put(term, 0);
		}
	}
	
	/** Retrieves all conversion results for all given params, or null if at least one param could not be resolved.
	 * All params that could not be resolved are pushed onto the todo stack. */
	private static ArrayList<Integer> getConvertedParamSizes(Term[] params, HashMap<Term, Integer> converted, ArrayDeque<Term> todo) {
		ArrayList<Integer> result = new ArrayList<Integer>();
		boolean foundAll = true;
		for (Term term : params) {
			Integer lookup = converted.get(term);
			if (lookup == null) {
				foundAll = false;
				todo.push(term);
			} else if (foundAll == true) {
				result.add(lookup);
			}
		}
		if (foundAll) return result;
		else return null;
	}
}
