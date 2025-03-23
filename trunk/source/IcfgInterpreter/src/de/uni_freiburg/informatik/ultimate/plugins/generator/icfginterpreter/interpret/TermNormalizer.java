package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiFunction;

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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;
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
	 * @param term A {@link BooleanTerm} representing the transformula of an ICFG edge.<br>
	 *             Should be obtained by {@link #parseTerm(Term, HashMap)}
	 * @return An {@link OrTerm} whose subTerms are all {@link AndTerm}s (DNF), each representing a different path that
	 *         can be taken in this edge. All xor and implies terms are broken up into their logical components. There
	 *         are no other {@link AndTerm} or {@link OrTerm}s. {@link ITETerm}s have their condition replaced by an
	 *         internal Variable Term. The first ancestor that is a BooleanTerm is then wrapped by
	 *         {@code (and ancestor (var = condition))}. Similar things are done for array select indexes and array
	 *         store indexes and values. This means that for example an IntegerTerm can only have children that are also
	 *         IntegerTerms or Variables, they do not contain internal BitVector, Array or Boolean terms.
	 */
	public static OrTerm simplifyToDNF(BooleanTerm term) {
		BooleanTerm simpleTerm = term.simplify();
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

				switch (restriction) {
				case final VariableBooleanTerm varBoolTerm:
					// and(..., bool_var, ...) = and(..., (bool_var = true), ...)
					restrictions.set(j, new EqualsTerm(restriction, new TrueTerm()).simplify());
					break;
				case final BooleanSelectTerm boolSelectTerm:
					// and(..., (select array_bool_var _), ...) = and(..., ((select array_bool_var _) = true), ...)
					restrictions.set(j, new EqualsTerm(restriction, new TrueTerm()).simplify());
					break;
				case final NotTerm notTerm:
					restriction = notTerm.getSubTerms().get(0);

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
					break;
				// The comparison terms may have constructs like (1 + var_a) <= var_b that can be simplified to
				// var_a < var_b
				case final LessEqualTerm leqTerm:
					break;
				case final LessTerm lsTerm:
					break;
				case final GreaterEqualTerm geqTerm:
					break;
				case final GreaterTerm gtTerm:
					break;
				default:
					break;
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
		final VariableTerm variableTerm = new VariableTerm(isInVar, isOutVar, isAuxVar, isAssignable, progVariable,
				termVariable);
		switch (ReturnType.getType(sort)) {
		case Array:
			final ReturnType valueType = ReturnType.getType(sort.getArguments()[1]);
			final ReturnType keyType = ReturnType.getType(sort.getArguments()[0]);
			return new VariableArrayTerm(keyType, valueType, variableTerm);
		case BitVector:
			// TODO
			break;
		case Boolean:
			return new VariableBooleanTerm(variableTerm);
		case Int:
			return new VariableIntegerTerm(variableTerm);
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
				return splitChained(parameters, (paramA, paramB) -> {
					assert paramA.returnType == paramB.returnType;
					return new EqualsTerm(paramA, paramB);
				});
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

				return splitChained(castToIntTerm(parameters), (paramA, paramB) -> {
					return new LessTerm(paramA, paramB);
				});
			case SMTLIBConstants.LEQ: // chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof IntegerTerm;
				}

				return splitChained(castToIntTerm(parameters), (paramA, paramB) -> {
					return new LessEqualTerm(paramA, paramB);
				});
			case SMTLIBConstants.GT: // chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof IntegerTerm;
				}

				return splitChained(castToIntTerm(parameters), (paramA, paramB) -> {
					return new GreaterTerm(paramA, paramB);
				});
			case SMTLIBConstants.GEQ: // chained
				for (final ExecutionTerm parameter : parameters) {
					assert parameter instanceof IntegerTerm;
				}

				return splitChained(castToIntTerm(parameters), (paramA, paramB) -> {
					return new GreaterEqualTerm(paramA, paramB);
				});

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

	public static <T> BooleanTerm splitChained(final T[] parameters, final BiFunction<T, T, BooleanTerm> convert) {
		assert parameters.length > 1;
		if (parameters.length == 2) {
			return convert.apply(parameters[0], parameters[1]);
		}

		final BooleanTerm[] chainedPairs = new BooleanTerm[parameters.length - 1];

		for (int i = 0; i < parameters.length - 1; i++) {
			chainedPairs[i] = convert.apply(parameters[i], parameters[i + 1]);
		}

		return new AndTerm(chainedPairs);
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
