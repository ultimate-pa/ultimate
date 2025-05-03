package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class FunctionContract {

	protected IPredicate mPrecondition;
	protected IPredicate mPostcondition;

	public FunctionContract(final IPredicate precondition, final IPredicate postcondition) {
		mPrecondition = precondition;
		mPostcondition = postcondition;
	}

	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	public Term transformPrecondition(final Summary summary, final ProgramUtilities<?> programUtilities) {
		final CfgSmtToolkit csToolkit = programUtilities.getCsToolkit();

		final Set<IProgramVar> callParams = programUtilities.getCallParams(summary);

		final Term transitionedPrecondition = programUtilities.callTransitionReverse(summary, mPrecondition);

		final Set<TermVariable> preconditionFreeVars = new HashSet<>();
		Collections.addAll(preconditionFreeVars, transitionedPrecondition.getFreeVars());

		final Collection<TermVariable> quantifiablePreconditionVars = preconditionFreeVars.stream()
				.filter(tv -> !callParams.contains(csToolkit.getSymbolTable().getProgramVar(tv))).toList();
		return SmtUtils.quantifier(csToolkit.getManagedScript().getScript(), QuantifiedFormula.EXISTS,
				quantifiablePreconditionVars, transitionedPrecondition);
	}

	public Term transformPostcondition(final Summary summary, final ProgramUtilities<?> programExtractor,
			final Map<IProgramVar, TermVariable> postReturnVarsMap) {
		final CfgSmtToolkit csToolkit = programExtractor.getCsToolkit();

		final Set<IProgramVar> callParams = programExtractor.getCallParams(summary);
		final Set<IProgramVar> returnParams = programExtractor.getReturnParams(summary);
		final Set<IProgramVar> callReturnParams = new HashSet<>(callParams);
		callReturnParams.addAll(returnParams);

		final Term transitionedPrecondition = programExtractor.callTransitionReverse(summary, mPrecondition);
		final IPredicate transitionedPreconditionPredicate =
				programExtractor.getPredicateFactory().newPredicate(transitionedPrecondition);

		final Term transitionedPostcondition =
				programExtractor.returnTransition(summary, mPostcondition, transitionedPreconditionPredicate);

		final Term transitionedPostcondition1 =
				programExtractor.returnTransition(summary, mPostcondition, mPrecondition);

		final UnmodifiableTransFormula callTransition = programExtractor.getCallTransition(summary);
		final UnmodifiableTransFormula returnTransition = programExtractor.getReturnTransition(summary);

		final Collection<TermVariable> prms = returnTransition.getInVars().values();

		final Term cal = programExtractor.getPredicateTransformer().pre(mPostcondition, callTransition);

		// final Term a =
		// programExtractor.getPredicateTransformer().strongestPostcondition(mPostcondition, returnTransition);

		// for (final TermVariable freeVar : cal.getFreeVars()) {
		// final IProgramVar programVar = csToolkit.getSymbolTable().getProgramVar(freeVar);
		// if (prms.contains(freeVar)) {
		// postconditionOutVarMap.put(freeVar, postReturnVarsMap.get(programVar));
		// }
		// }

		// There probably is a better way to get return var mapping
		final List<List<IProgramVar>> equalities = ProgramUtilities.getEqualities(returnTransition);
		final Map<TermVariable, TermVariable> eqMap = new HashMap<>();

		for (final TermVariable tv : mPostcondition.getFormula().getFreeVars()) {
			final IProgramVar pv = csToolkit.getSymbolTable().getProgramVar(tv);

			for (final List<IProgramVar> eq : equalities) {
				if (eq.contains(pv)) {
					final IProgramVar other = eq.get(0).equals(pv) ? eq.get(1) : eq.get(0);
					eqMap.put(tv, other.getTermVariable());
					break;
				}

			}
		}

		final Map<TermVariable, TermVariable> substitutionMap = new HashMap<>();
		for (final var entry : eqMap.entrySet()) {
			final TermVariable origin = entry.getKey();
			final TermVariable target = entry.getValue();

			final IProgramVar targetProgramVar = csToolkit.getSymbolTable().getProgramVar(target);
			final TermVariable subVar = postReturnVarsMap.get(targetProgramVar);

			substitutionMap.put(origin, subVar);

		}

		final Term substitutedPostcondition = Substitution.apply(csToolkit.getManagedScript(), substitutionMap, cal);

		// final IPredicate subb = programExtractor.getPredicateFactory().newPredicate(substitutedPostcondition);

		// final Term b = programExtractor.getPredicateTransformer().pre(subb, callTransition);

		final Set<TermVariable> postconditionFreeVars = new HashSet<>();
		Collections.addAll(postconditionFreeVars, substitutedPostcondition.getFreeVars());

		final Collection<TermVariable> quantifiablePostconditionVars = postconditionFreeVars.stream()
				.filter(tv -> !callReturnParams.contains(csToolkit.getSymbolTable().getProgramVar(tv))
						&& !postReturnVarsMap.containsValue(tv))
				.toList();
		return SmtUtils.quantifier(csToolkit.getManagedScript().getScript(), QuantifiedFormula.EXISTS,
				quantifiablePostconditionVars, substitutedPostcondition);
	}

	public static UnmodifiableTransFormula buildTransFormulaForContract(final Summary summary,
			final FunctionContract contract, final ProgramUtilities<?> programUtilities) {

		final Collection<FunctionContract> contracts = new HashSet<>();
		contracts.add(contract);
		return buildTransFormulaForContracts(summary, contracts, programUtilities);
	}

	public static UnmodifiableTransFormula buildTransFormulaForContracts(final Summary summary,
			final Collection<FunctionContract> contracts, final ProgramUtilities<?> programUtilities) {
		final CfgSmtToolkit csToolkit = programUtilities.getCsToolkit();

		final Set<IProgramVar> callParams = programUtilities.getCallParams(summary);
		final Set<IProgramVar> returnParams = programUtilities.getReturnParams(summary);

		final UnmodifiableTransFormula callTransition = programUtilities.getCallTransition(summary);
		final UnmodifiableTransFormula returnTransition = programUtilities.getReturnTransition(summary);

		final Collection<TermVariable> prms = returnTransition.getInVars().values();

		final Map<IProgramVar, TermVariable> postReturnVarsMap = new HashMap<>();
		for (final IProgramVar returnParam : returnParams) {
			final TermVariable termVariable = csToolkit.getManagedScript().constructFreshTermVariable(
					returnParam.getTermVariable().getName() + "_post", returnParam.getSort());

			postReturnVarsMap.put(returnParam, termVariable);
		}

		final Set<Term> implications = new HashSet<>();

		for (final FunctionContract contract : contracts) {
			final Term transformedPrecondition = contract.transformPrecondition(summary, programUtilities);
			final Term transformedPostcondition =
					contract.transformPostcondition(summary, programUtilities, postReturnVarsMap);

			final Term implication = SmtUtils.implies(csToolkit.getManagedScript().getScript(), transformedPrecondition,
					transformedPostcondition);

			implications.add(implication);
		}

		final Term formula = SmtUtils.and(csToolkit.getManagedScript().getScript(), implications);

		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();

		for (final IProgramVar callParam : callParams) {
			final TermVariable termVariable = callParam.getTermVariable();
			inVars.put(callParam, termVariable);
			if (!returnParams.contains(callParam)) {
				outVars.put(callParam, termVariable);
			}
		}

		for (final IProgramVar returnParam : returnParams) {
			final TermVariable termVariable = postReturnVarsMap.get(returnParam);
			outVars.put(returnParam, termVariable);
		}

		final TransFormulaBuilder builder = new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);

		builder.setFormula(formula);
		builder.setInfeasibility(Infeasibility.UNPROVEABLE);

		return builder.finishConstruction(csToolkit.getManagedScript());

	}

	public static UnmodifiableTransFormula buildAssureTransFormula(final Summary summary,
			final Collection<FunctionContract> contracts, final ProgramUtilities<?> programUtilities) {
		final CfgSmtToolkit csToolkit = programUtilities.getCsToolkit();

		final Set<Term> preconditions = new HashSet<>();

		for (final FunctionContract contract : contracts) {
			final Term precondition = contract.transformPrecondition(summary, programUtilities);
			preconditions.add(precondition);
		}

		final Term orTerm = SmtUtils.or(csToolkit.getManagedScript().getScript(), preconditions);
		final Term formula = SmtUtils.not(csToolkit.getManagedScript().getScript(), orTerm);

		final Map<IProgramVar, TermVariable> inOutVars = new HashMap<>();
		for (final TermVariable freeVar : formula.getFreeVars()) {
			final IProgramVar programVar = csToolkit.getSymbolTable().getProgramVar(freeVar);
			inOutVars.put(programVar, freeVar);
		}

		final TransFormulaBuilder builder = new TransFormulaBuilder(inOutVars, inOutVars, true, null, true, null, true);

		builder.setFormula(formula);
		builder.setInfeasibility(Infeasibility.UNPROVEABLE);

		return builder.finishConstruction(csToolkit.getManagedScript());
	}

	@Override
	public String toString() {
		return "[" + mPrecondition + " -> " + mPostcondition + "]";
	}

}
