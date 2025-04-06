package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ICFGExecutionEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.ArrayITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.StoreTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.AndTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.BoolITETerm;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.XorTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.SelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.AbsoluteTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.AdditionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.ConstIntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.DivisionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.IntITETerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.ModuloTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.MultiplicationTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.NegationTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.SubtractionTerm;

public class IcfgTranslation {
	public static OrTerm translateTerm(final UnmodifiableTransFormula transFormula) throws Exception {
		final VariableSet variables = getVariables(transFormula);

		final ExecutionTerm term = parseTerm(transFormula.getFormula(), variables);

		if (!(term instanceof BooleanTerm)) {
			throw new Exception("Formula " + transFormula.toString() + " is not a valid transition term.");
		}

		return TermNormalizer.simplifyToDNF((BooleanTerm) term);
	}

	private static HashMap<UnmodifiableTransFormula, VariableSet> cache = new HashMap<>();

	public static VariableSet getVariables(final UnmodifiableTransFormula formula) {
		final VariableSet vars = cache.getOrDefault(formula, null);
		if (vars != null) {
			return vars;
		}
		final VariableSet out = new VariableSet();

		final Set<IProgramVar> assignable = formula.getAssignedVars();
		final Map<IProgramVar, TermVariable> inVars = formula.getInVars();
		final Map<IProgramVar, TermVariable> outVars = formula.getOutVars();

		for (final Entry<IProgramVar, TermVariable> progVar : inVars.entrySet()) {
			final IProgramVar progVariable = progVar.getKey();
			final TermVariable termVariable = progVar.getValue();

			final boolean isOutVar = outVars.containsValue(termVariable);
			final boolean isAssignable = assignable.contains(progVariable);

			out.addVariable(true, isOutVar, false, isAssignable, progVariable, termVariable);
		}

		for (final Entry<IProgramVar, TermVariable> progVar : outVars.entrySet()) {
			final IProgramVar progVariable = progVar.getKey();
			final TermVariable termVariable = progVar.getValue();

			final boolean isInVar = inVars.containsValue(termVariable);
			final boolean isAssignable = assignable.contains(progVariable);

			out.addVariable(isInVar, true, false, isAssignable, progVariable, termVariable);
		}

		for (final TermVariable termVariable : formula.getAuxVars()) {
			out.addVariable(false, false, true, true, null, termVariable);
		}

		return out;
	}

	/**
	 * Translates the ICFG using breadth first search.
	 *
	 * @throws Exception
	 */
	public static InterpretedIcfg parseIcfg(final IIcfg<? extends IcfgLocation> icfg,
			final IUltimateServiceProvider services) throws Exception {
		final Set<? extends IcfgLocation> initialNodes = icfg.getInitialNodes();
		final ManagedScript script = icfg.getCfgSmtToolkit().getManagedScript();

		final InterpretedIcfg out = new InterpretedIcfg();

		final HashSet<IcfgLocation> visited = new HashSet<>();
		final ArrayList<IcfgLocation> next = new ArrayList<>(initialNodes);

		while (next.size() > 0) {
			final IcfgLocation source = next.remove(0);

			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();

				if (!visited.contains(target)) {
					next.add(target);
					visited.add(source);
				}

				final ArrayList<ICFGExecutionEdge> execEdges = parseEdges(edge.getTransformula(), source, target,
						script, services);

				for (final ICFGExecutionEdge execEdge : execEdges) {
					out.addEdge(execEdge);
				}
			}
		}

		return out;
	}

	private static final OrTerm falseGuard = new OrTerm(new AndTerm(new FalseTerm()));

	/**
	 * Creates edges representing each path through this transition should there be more than one (in DNF form achieved
	 * by {@link TermNormalizer#simplifyToDNF(BooleanTerm)}
	 *
	 * @param transFormula
	 * @param source
	 * @param target
	 * @param managedScript
	 * @param service
	 * @return
	 * @throws Exception
	 */
	public static ArrayList<ICFGExecutionEdge> parseEdges(final UnmodifiableTransFormula transFormula,
			final IcfgLocation source, final IcfgLocation target, final ManagedScript managedScript,
			final IUltimateServiceProvider service) throws Exception {
		final VariableSet variables = getVariables(transFormula);

		final Theory formulaTheory = transFormula.getFormula().getTheory();

		final UnmodifiableTransFormula guardFormula = TransFormulaUtils.computeGuard(transFormula, managedScript,
				service);

		final OrTerm term = translateTerm(transFormula);
		final OrTerm guardTerm = translateTerm(guardFormula);

		if (falseGuard.equals(guardTerm)) {
			return new ArrayList<>(); // edge can never be taken, no need to return it for execution
		}

		final ArrayList<BooleanTerm> andTerms = term.getSubTerms();

		final HashMap<ArcSolver, AndTerm> arcSolvers = new HashMap<>();

		int constrainingArcs = 0;
		for (final BooleanTerm child : andTerms) {
			final AndTerm andChild = (AndTerm) child;
			final ArcSolver newSolver = new ArcSolver(andChild, managedScript, variables, formulaTheory);
			constrainingArcs += newSolver.hasConstraints() ? 1 : 0;
			arcSolvers.put(newSolver, andChild);
		}

		final ArrayList<ICFGExecutionEdge> edges = new ArrayList<>();
		if (constrainingArcs == 0) {
			// all ways to the next state have no updates, make trivial arc with the guard of the whole term
			final ArcSolver trivialArc = new ArcSolver(new AndTerm(new TrueTerm()), managedScript, variables,
					formulaTheory);
			edges.add(new ICFGExecutionEdge(transFormula, source, target, variables, trivialArc, guardTerm, "A"));

			return edges;
		}

		final Infeasibility isInfeasable = guardFormula.isInfeasible();
		final Set<TermVariable> branchEncoders = guardFormula.getBranchEncoders();

		int i = 0;
		for (final Entry<ArcSolver, AndTerm> entry : arcSolvers.entrySet()) {
			final UnmodifiableTransFormula arcGuardFormula = entry.getKey().makeGuardFormula(managedScript, service,
					entry.getValue().toSMTTerm(formulaTheory), isInfeasable, branchEncoders);
			final OrTerm arcGuardTerm = TermNormalizer
					.simplifyToDNF((BooleanTerm) parseTerm(arcGuardFormula.getFormula(), variables));

			if (falseGuard.equals(arcGuardTerm)) {
				continue; // edge can never be taken, no need to return it for execution
			}

			final String edgeID = Util.intToLetters(i);
			i++;

			final ICFGExecutionEdge newEdge = new ICFGExecutionEdge(transFormula, source, target, variables,
					entry.getKey(), arcGuardTerm, edgeID);
			edges.add(newEdge);
		}
		return edges;
	}

	public static ExecutionTerm parseTerm(final Term term, final VariableSet variables) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm termApp = (ApplicationTerm) term;

			final Term[] unparsedParameters = termApp.getParameters();
			final ExecutionTerm[] parameters = new ExecutionTerm[unparsedParameters.length];
			for (int i = 0; i < unparsedParameters.length; i++) {
				parameters[i] = parseTerm(unparsedParameters[i], variables);
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
			return variables.getVariable((TermVariable) term).getTerm();
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
