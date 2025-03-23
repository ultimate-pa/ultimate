package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public abstract class ExecutionTerm {
	public enum ReturnType {
		Boolean, Int, Array, BitVector;

		public static ReturnType getType(final Sort sort) {
			switch (sort.getName()) {
			case "Array":
				return Array;
			case "BitVec":
				return BitVector;
			case "Bool":
				return Boolean;
			case "Int":
				return Int;
			}
			assert false;
			return null;
		}
	}

	public final ReturnType returnType;
	public final String mSymbol;

	public ExecutionTerm(final ReturnType mReturnType, final String symbol) {
		returnType = mReturnType;
		mSymbol = symbol;
	}

	public abstract Term toSMTTerm(Theory theory);

	public abstract ExecutionTerm simplify();

	public abstract ArrayList<? extends ExecutionTerm> getSubTerms();

	protected abstract HashSet<Variable> getVariablesInternal();

	protected HashSet<Variable> variables = null;

	public HashSet<Variable> getVariables() {
		if (variables == null) {
			variables = getVariablesInternal();
		}
		return Util.copySet(variables);
	}

	public abstract Object evaluate(ProgramState currentState, ProgramState nextState);

	public boolean containsVariable(final Variable var) {
		return getVariables().contains(var);
	}

	@Override
	public abstract boolean equals(Object b);

	@Override
	public abstract int hashCode();

	public abstract StringBuilder toString(StringBuilder out, int depth);

	@Override
	public String toString() {
		return toString(new StringBuilder(""), 0).toString();
	}
}
