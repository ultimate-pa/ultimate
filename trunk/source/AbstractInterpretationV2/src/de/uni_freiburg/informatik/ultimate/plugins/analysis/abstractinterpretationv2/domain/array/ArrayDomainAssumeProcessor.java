package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;

public class ArrayDomainAssumeProcessor<STATE extends IAbstractState<STATE>> {
	private final ArrayDomainToolkit<STATE> mToolkit;

	public ArrayDomainAssumeProcessor(final ArrayDomainToolkit<STATE> toolkit) {
		mToolkit = toolkit;
	}

	public ArrayDomainState<STATE> process(final ArrayDomainState<STATE> oldState, final Expression assumption) {
		ArrayDomainState<STATE> returnState = oldState;
		final Term cnf = SmtUtils.toCnf(mToolkit.getServices(), mToolkit.getManagedScript(),
				mToolkit.getTerm(assumption), XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		for (final Term t : SmtUtils.getConjuncts(cnf)) {
			if (returnState.isBottom()) {
				break;
			}
			returnState = processTerm(returnState, t);
		}
		return returnState;
	}

	private ArrayDomainState<STATE> processTerm(final ArrayDomainState<STATE> state, final Term assumption) {
		assert !SmtUtils.isFunctionApplication(assumption, "and");
		if (SmtUtils.isFunctionApplication(assumption, "or")) {
			ArrayDomainState<STATE> returnState = mToolkit.createBottomState();
			for (final Term t : ((ApplicationTerm) assumption).getParameters()) {
				returnState = returnState.union(processTerm(returnState, t));
			}
			return returnState;
		}
		final Script script = mToolkit.getScript();
		if (containsArrayEquality(assumption)) {
			// TODO: handle array (in)equalities
			return state;
		}
		final List<Term> constraints = new ArrayList<>();
		final SegmentationMap newSegmentationMap = state.getSegmentationMap();
		final Map<Term, Term> substitution = new HashMap<>();
		final List<IProgramVarOrConst> newVariables = new ArrayList<>();
		for (final MultiDimensionalSelect select : MultiDimensionalSelect.extractSelectShallow(assumption, false)) {
			// TODO: Replace array-assumptions
		}
		constraints.add(new Substitution(mToolkit.getManagedScript(), substitution).transform(assumption));
		final STATE newSubState = mToolkit.handleAssumptionBySubdomain(state.getSubState().addVariables(newVariables),
				SmtUtils.and(script, constraints));
		return state.updateState(newSubState, newSegmentationMap).simplify();
	}

	private boolean containsArrayEquality(final Term term) {
		if (!(term instanceof ApplicationTerm)) {
			return false;
		}
		final ApplicationTerm appl = (ApplicationTerm) term;
		final String functionName = appl.getFunction().getApplicationString();
		final Term[] params = appl.getParameters();
		if ("not".equals(functionName)) {
			return containsArrayEquality(params[0]);
		}
		return "=".equals(functionName) && params[0].getSort().isArraySort();
	}
}
