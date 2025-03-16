package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.ArrayITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.StoreTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.AndTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.BoolITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.BooleanSelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.DistinctTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.EqualsTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.FalseTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.GreaterEqualTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.GreaterTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.ImpliesTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.LessEqualTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.LessTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.NotTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.OrTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.TrueTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.XorTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.ITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.SelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.AbsoluteTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.AdditionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.ConstIntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.DivisionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.IntITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.ModuloTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.MultiplicationTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.NegationTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.SubtractionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

public class TermNormalizer {
	/**
	 * For a term that contains an ite term: This method swaps the condition of the term with an auxiliary variable, and
	 * wraps the first parent boolean term with (and parentOfITE, (aux_bool_var = condition))
	 *
	 * @param term
	 * @param conditions
	 * @return / private static ExecutionTerm replaceITEwithAux(ExecutionTerm term) { for (final ExecutionTerm subTerm :
	 *         term.getSubTerms()) { term = replaceSubTerm(term, subTerm); }
	 *
	 *         if (term instanceof ITE) { ITE iteTerm = (ITE) term; final ArrayList<ExecutionTerm> auxEquality = new
	 *         ArrayList<>(); final VariableBooleanTerm auxReplacement = makeNextAux(); iteTerm =
	 *         iteTerm.replaceCondition(auxReplacement);
	 *
	 *         final EqualsTerm auxEQ = new EqualsTerm(auxReplacement, iteTerm.getCondition()); if
	 *         (!aux_equivalences.contains(auxEQ)) { aux_equivalences.add(auxEQ); } }
	 *
	 *         if (term instanceof BooleanTerm && aux_equivalences.size() > 1) { // we can wrap the built up
	 *         equivalences around this term final BooleanTerm[] outArray = new BooleanTerm[aux_equivalences.size() +
	 *         1]; outArray[0] = (BooleanTerm) term; for (int i = 0; i < aux_equivalences.size(); i++) { outArray[i + 1]
	 *         = aux_equivalences.get(i); } return new AndTerm(outArray); }
	 *
	 *         return term; }
	 *
	 *         private static ArrayList<EqualsTerm> aux_equivalences; private static int auxNameCounter;
	 *
	 *         private static VariableBooleanTerm makeNextAux() { final String name = "INTERNAL_BOOL_AUX_" +
	 *         auxNameCounter; auxNameCounter++; final Sort boolSort = Util.getTheory().getBooleanSort(); final
	 *         TermVariable auxTerm = Util.getTheory().createTermVariable(name, boolSort); return new
	 *         VariableBooleanTerm(false, true, true, true, null, auxTerm); }
	 *
	 *         private static ExecutionTerm replaceSubTerm(final ExecutionTerm term, final ExecutionTerm subTerm) {
	 *         final ExecutionTerm newSubTerm = replaceITEwithAux(subTerm); if (newSubTerm.equals(subTerm)) { return
	 *         term; } return term.replaceSubTerm(subTerm, newSubTerm); }
	 */

	/**
	 *
	 * @param term A {@link BooleanTerm} representing the transformula of an ICFG edge.<br>
	 *             Should be obtained by {@link #parseTerm(Term, HashMap)}
	 * @return An {@link OrTerm} whose subTerms are all {@link AndTerm}s, each representing a different path that can be
	 *         taken in this edge. All xor and implies terms are broken up into their logical components. There are no
	 *         other {@link AndTerm} or {@link OrTerm}s. {@link ITETerm}s have their condition replaced by an internal
	 *         Variable Term. The first ancestor that is a BooleanTerm is then wrapped by
	 *         {@code (and ancestor (var = condition))}. Similar things are done for array select indexes and array
	 *         store indexes and values. This means that for example an IntegerTerm can only have children that are also
	 *         IntegerTerms or Variables, they do not contain internal BitVector, Array or Boolean terms.
	 */
	public static OrTerm normalize(BooleanTerm term) {
		// auxNameCounter = 0;
		// aux_equivalences = new ArrayList<>();
		// final BooleanTerm itelessTerm = (BooleanTerm) replaceITEwithAux(term);

		BooleanTerm simpleTerm = /* itelessTerm */term.simplify();
		while (!simpleTerm.equals(term)) {
			term = simpleTerm;
			simpleTerm = term.simplify();
		}

		ArrayList<BooleanTerm> andTerms = new ArrayList<>();
		if (simpleTerm instanceof OrTerm) {
			andTerms = ((OrTerm) simpleTerm).getSubTerms();
		} else {
			andTerms.add(simpleTerm);
		}

		for (int i = 0; i < andTerms.size(); i++) {
			BooleanTerm andTerm = andTerms.get(i);
			if (!(andTerm instanceof AndTerm)) {
				andTerm = new AndTerm(andTerm);
			}
			final ArrayList<BooleanTerm> restrictions = ((AndTerm) andTerm).getSubTerms();

			for (int j = 0; j < restrictions.size(); j++) {
				BooleanTerm restriction = restrictions.get(j);

				// and(..., bool_var, ...) = and(..., (bool_var = true), ...)
				if (restriction instanceof VariableBooleanTerm) {
					restrictions.set(j, new EqualsTerm(restriction, new TrueTerm()).simplify());
					continue;
				}

				// and(..., (select array_bool_var _), ...) = and(..., ((select array_bool_var _) = true), ...)
				if (restriction instanceof BooleanSelectTerm) {
					restrictions.set(j, new EqualsTerm(restriction, new TrueTerm()).simplify());
					continue;
				}

				if (restriction instanceof NotTerm) {
					restriction = ((NotTerm) restriction).getSubTerms().get(0);

					// and(..., (not bool_var), ...) = and(..., (bool_var = false), ...)
					if (restriction instanceof VariableBooleanTerm) {
						restrictions.set(j, new EqualsTerm(restriction, new FalseTerm()).simplify());
						continue;
					}

					// and(..., (not (select array_bool_var _)), ...) = and(..., ((select array_bool_var _) = false),
					// ...)
					if (restriction instanceof BooleanSelectTerm) {
						restrictions.set(j, new EqualsTerm(restriction, new FalseTerm()).simplify());
						continue;
					}
				}
			}

			andTerms.set(i, new AndTerm(restrictions.toArray(new BooleanTerm[restrictions.size()])));
		}
		return new OrTerm(andTerms.toArray(new AndTerm[andTerms.size()]));
	}

	public static BooleanTerm eliminateITE(final BooleanTerm term) {
		return term; // TODO
	}

	private static Variable getVariable(final boolean isInVar, final boolean isOutVar, final boolean isAuxVar,
			final boolean isAssignable, final IProgramVar progVariable, final TermVariable termVariable) {
		final Sort sort = termVariable.getDeclaredSort();
		switch (ReturnType.getType(sort)) {
		case Array:
			final ReturnType valueType = ReturnType.getType(sort.getArguments()[1]);
			final ReturnType keyType = ReturnType.getType(sort.getArguments()[0]);
			return new VariableArrayTerm(keyType, valueType, isInVar, isOutVar, isAuxVar, isAssignable, progVariable,
					termVariable);
		case BitVector:
			// TODO
			break;
		case Boolean:
			return new VariableBooleanTerm(isInVar, isOutVar, isAuxVar, isAssignable, progVariable, termVariable);
		case Int:
			return new VariableIntegerTerm(isInVar, isOutVar, isAuxVar, isAssignable, progVariable, termVariable);
		}
		return null;
	}

	public static HashMap<TermVariable, Variable> getVariables(final UnmodifiableTransFormula formula) {
		final HashMap<TermVariable, Variable> vars = new HashMap<>();

		final Set<IProgramVar> assignable = formula.getAssignedVars();

		final HashMap<IProgramVar, TermVariable> inVars = new HashMap<>(formula.getInVars());
		final HashMap<IProgramVar, TermVariable> outVars = new HashMap<>(formula.getOutVars());

		for (final Entry<IProgramVar, TermVariable> progVar : inVars.entrySet()) {
			final IProgramVar progVariable = progVar.getKey();
			final TermVariable termVariable = progVar.getValue();

			final boolean isInVar = true;
			final boolean isOutVar = outVars.containsValue(termVariable);
			final boolean isAuxVar = false;
			final boolean isAssignable = assignable.contains(progVariable);

			final Variable out = getVariable(isInVar, isOutVar, isAuxVar, isAssignable, progVariable, termVariable);

			vars.put(termVariable, out);
		}

		for (final Entry<IProgramVar, TermVariable> progVar : outVars.entrySet()) {
			final IProgramVar progVariable = progVar.getKey();
			final TermVariable termVariable = progVar.getValue();

			final boolean isInVar = inVars.containsValue(termVariable);
			final boolean isOutVar = true;
			final boolean isAuxVar = false;
			final boolean isAssignable = assignable.contains(progVariable);

			final Variable out = getVariable(isInVar, isOutVar, isAuxVar, isAssignable, progVariable, termVariable);

			vars.put(termVariable, out);
		}

		for (final TermVariable auxVar : formula.getAuxVars()) {
			final boolean isInVar = false;
			final boolean isOutVar = false;
			final boolean isAuxVar = true;
			final boolean isAssignable = true;

			final Variable out = getVariable(isInVar, isOutVar, isAuxVar, isAssignable, null, auxVar);

			vars.put(auxVar, out);
		}

		return vars;
	}

	public static ExecutionTerm parseTerm(final Term term, final HashMap<TermVariable, Variable> vars) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm termApp = (ApplicationTerm) term;

			final Term[] unparsedParameters = termApp.getParameters();
			final ExecutionTerm[] parameters = new ExecutionTerm[unparsedParameters.length];
			for (int i = 0; i < unparsedParameters.length; i++) {
				parameters[i] = parseTerm(unparsedParameters[i], vars);
			}

			switch (termApp.getFunction().getName()) {
			case SMTLIBConstants.TRUE:
				return new TrueTerm();
			case SMTLIBConstants.FALSE:
				return new FalseTerm();
			case SMTLIBConstants.NOT:
				assert parameters[0] instanceof BooleanTerm;
				return new NotTerm((BooleanTerm) parameters[0]);
			case SMTLIBConstants.IMPLIES:
				// right associative
				// (=> A B C D) is (A => (B => (C => D)))
				int lastElement = parameters.length - 1;

				assert parameters[lastElement] instanceof BooleanTerm;
				assert parameters[lastElement - 1] instanceof BooleanTerm;

				ImpliesTerm impliesBracketed = new ImpliesTerm((BooleanTerm) parameters[lastElement - 1],
						(BooleanTerm) parameters[lastElement]);

				lastElement -= 2;

				for (; 0 <= lastElement; lastElement--) {
					assert parameters[lastElement] instanceof BooleanTerm;
					impliesBracketed = new ImpliesTerm((BooleanTerm) parameters[lastElement], impliesBracketed);
				}
				return impliesBracketed;
			case SMTLIBConstants.AND: // left associative, chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof BooleanTerm;
				}
				return new AndTerm(castToBoolTerm(parameters));
			case SMTLIBConstants.OR: // left associative, chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof BooleanTerm;
				}
				return new OrTerm(castToBoolTerm(parameters));
			case SMTLIBConstants.XOR:
				// left associative
				// (xor A B C D) is (((A xor B) xor C) xor D)

				assert parameters[0] instanceof BooleanTerm;
				assert parameters[1] instanceof BooleanTerm;

				XorTerm xorBracketed = new XorTerm((BooleanTerm) parameters[0], (BooleanTerm) parameters[1]);

				for (int i = 2; i < parameters.length; i++) {
					assert parameters[i] instanceof BooleanTerm;
					xorBracketed = new XorTerm(xorBracketed, (BooleanTerm) parameters[i]);
				}
				return xorBracketed;
			case SMTLIBConstants.EQUALS:
				return getEqualsTerm(parameters);
			case SMTLIBConstants.DISTINCT:
				return getDistinctTerm(parameters);
			case SMTLIBConstants.ITE:
				assert parameters[0] instanceof BooleanTerm;
				assert parameters[1].returnType == parameters[2].returnType;

				final BooleanTerm condition = (BooleanTerm) parameters[0];

				switch (parameters[1].returnType) {
				case Array:
					final ArrayTerm ifArray = (ArrayTerm) parameters[1];
					final ArrayTerm elseArray = (ArrayTerm) parameters[2];
					return new ArrayITETerm(condition, ifArray, elseArray);
				case BitVector:
					// TODO
					break;
				case Boolean:
					final BooleanTerm ifBool = (BooleanTerm) parameters[1];
					final BooleanTerm elseBool = (BooleanTerm) parameters[2];
					return new BoolITETerm(condition, ifBool, elseBool);
				case Int:
					final IntegerTerm ifInt = (IntegerTerm) parameters[1];
					final IntegerTerm elseInt = (IntegerTerm) parameters[2];
					return new IntITETerm(condition, ifInt, elseInt);
				}
				assert false;
				return null;

			case SMTLIBConstants.STORE:
				assert parameters[0] instanceof ArrayTerm;
				assert !(parameters[1] instanceof ArrayTerm);

				final ArrayTerm storageArray = (ArrayTerm) parameters[0];

				return new StoreTerm(storageArray, parameters[1], parameters[2]);
			case SMTLIBConstants.SELECT:
				assert parameters[0] instanceof ArrayTerm;
				assert !(parameters[1] instanceof ArrayTerm);

				final ArrayTerm selectArray = (ArrayTerm) parameters[0];

				return SelectTerm.getSelectTerm(selectArray, parameters[1]);

			case SMTLIBConstants.MINUS:
				// (- x) (Negation)
				if (parameters.length == 1) {
					assert parameters[0] instanceof IntegerTerm;
					return new NegationTerm((IntegerTerm) parameters[0]);
				}

				// left associative, chained (Minus)
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof BooleanTerm;
				}

				return new SubtractionTerm(castToIntTerm(parameters));
			case SMTLIBConstants.PLUS:
				// left associative, chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof IntegerTerm;
				}

				return new AdditionTerm(castToIntTerm(parameters));
			case SMTLIBConstants.MUL:
				// left associative, chained
				return new MultiplicationTerm(castToIntTerm(parameters));
			case SMTLIBConstants.DIV:
				// left associative, chained
				// (div A B C D) is (((A div B) div C) div D)
				assert parameters[0] instanceof IntegerTerm;
				assert parameters[1] instanceof IntegerTerm;

				DivisionTerm divBracketed = new DivisionTerm((IntegerTerm) parameters[0], (IntegerTerm) parameters[1]);

				for (int i = 2; i < parameters.length; i++) {
					assert parameters[i] instanceof IntegerTerm;
					divBracketed = new DivisionTerm(divBracketed, (IntegerTerm) parameters[i]);
				}
				return divBracketed;
			case SMTLIBConstants.MOD: // exactly two parameters
				assert parameters[0] instanceof IntegerTerm;
				assert parameters[1] instanceof IntegerTerm;

				return new ModuloTerm((IntegerTerm) parameters[0], (IntegerTerm) parameters[1]);
			case SMTLIBConstants.ABS:// exactly one parameter
				assert parameters[0] instanceof IntegerTerm;

				return new AbsoluteTerm((IntegerTerm) parameters[0]);
			case SMTLIBConstants.LT: // chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof IntegerTerm;
				}

				return new LessTerm(castToIntTerm(parameters));
			case SMTLIBConstants.LEQ: // chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof IntegerTerm;
				}

				return new LessEqualTerm(castToIntTerm(parameters));
			case SMTLIBConstants.GT: // chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof IntegerTerm;
				}

				return new GreaterTerm(castToIntTerm(parameters));
			case SMTLIBConstants.GEQ: // chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof IntegerTerm;
				}

				return new GreaterEqualTerm(castToIntTerm(parameters));

			// TODO Bit Vecs
			}
		} else if (term instanceof ConstantTerm) {
			final ConstantTerm termConst = (ConstantTerm) term;
			final Object valueUnparsed = termConst.getValue();
			final Sort sort = termConst.getSort();

			switch (sort.getName()) {
			case SMTLIBConstants.INT:
				int value;
				if (valueUnparsed instanceof Rational) {
					final Rational valueParsed = (Rational) valueUnparsed;
					value = (valueParsed.numerator().divide(valueParsed.denominator())).intValueExact();

				} else if (valueUnparsed instanceof BigInteger) {
					value = ((BigInteger) valueUnparsed).intValue();
				} else {
					value = (int) valueUnparsed;
				}
				return new ConstIntegerTerm(value);
			case SMTLIBConstants.BOOL:
				if ((boolean) valueUnparsed) {
					return new TrueTerm();
				}
				return new FalseTerm();
			case SMTLIBConstants.BITVEC:
				return null;
			/*
			 * TODO int length = Integer.parseInt(termConst.getSort().getIndices()[0]); value =
			 * BitVector.fromBigInt((BigInteger) valueUnparsed, length);
			 */
			}
		} else if (term instanceof TermVariable) {
			return vars.get(term).getTerm();
		}

		return null;
	}

	private static BooleanTerm getDistinctTerm(final ExecutionTerm[] parameters) {
		final int length = (parameters.length * (parameters.length - 1)) / 2;
		final DistinctTerm[] inequals = new DistinctTerm[length];

		int index = 0;
		for (int i = 0; i < parameters.length - 1; i++) {
			assert parameters[i].returnType == parameters[i + 1].returnType;

			for (int j = i + 1; j < parameters.length; j++) {
				inequals[index] = new DistinctTerm(parameters[i], parameters[j]);
				index++;
			}
		}

		if (parameters.length == 2) {
			return inequals[0];
		}

		return new AndTerm(inequals);
	}

	private static BooleanTerm getEqualsTerm(final ExecutionTerm[] parameters) {
		final EqualsTerm[] equals = new EqualsTerm[parameters.length - 1];

		for (int i = 0; i < parameters.length - 1; i++) {
			assert parameters[i].returnType == parameters[i + 1].returnType;
			equals[i] = new EqualsTerm(parameters[i], parameters[i + 1]);
		}

		if (parameters.length == 2) {
			return equals[0];
		}

		return new AndTerm(equals);
	}

	/*
	 * public static <D extends Domain<D>> Term<D>[] castByReturnType(ReturnType type, Term<?>[] parameters) {
	 * switch(type) { case Array: break; case BitVector: break; case Boolean: return (BooleanTerm); break; case Int:
	 * break; default: break; } }
	 */

	public static IntegerTerm[] castToIntTerm(final ExecutionTerm[] terms) {
		final IntegerTerm[] out = new IntegerTerm[terms.length];
		for (int i = 0; i < terms.length; i++) {
			assert terms[i] instanceof IntegerTerm;
			out[i] = (IntegerTerm) terms[i];
		}
		return out;
	}

	private static BooleanTerm[] castToBoolTerm(final ExecutionTerm[] terms) {
		final BooleanTerm[] out = new BooleanTerm[terms.length];
		for (int i = 0; i < terms.length; i++) {
			assert terms[i] instanceof BooleanTerm;
			out[i] = (BooleanTerm) terms[i];
		}
		return out;
	}
}
