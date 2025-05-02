package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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

		final Set<TermVariable> postconditionFreeVars = new HashSet<>();
		Collections.addAll(postconditionFreeVars, transitionedPostcondition.getFreeVars());

		final Collection<TermVariable> quantifiablePostconditionVars = postconditionFreeVars.stream()
				.filter(tv -> !callReturnParams.contains(csToolkit.getSymbolTable().getProgramVar(tv))).toList();
		final Term quantifiedPostcondition = SmtUtils.quantifier(csToolkit.getManagedScript().getScript(),
				QuantifiedFormula.EXISTS, quantifiablePostconditionVars, transitionedPostcondition);

		final Map<TermVariable, TermVariable> postconditionOutVarMap = new HashMap<>();
		for (final TermVariable freeVar : quantifiedPostcondition.getFreeVars()) {
			final IProgramVar programVar = csToolkit.getSymbolTable().getProgramVar(freeVar);
			if (returnParams.contains(programVar)) {
				postconditionOutVarMap.put(freeVar, postReturnVarsMap.get(programVar));
			}
		}

		return Substitution.apply(csToolkit.getManagedScript(), postconditionOutVarMap, quantifiedPostcondition);
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
