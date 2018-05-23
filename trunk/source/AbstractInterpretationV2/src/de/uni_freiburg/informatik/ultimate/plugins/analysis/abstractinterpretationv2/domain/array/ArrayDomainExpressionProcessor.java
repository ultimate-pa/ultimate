package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ArrayDomainExpressionProcessor<STATE extends IAbstractState<STATE>> {
	private final ArrayDomainToolkit<STATE> mToolkit;

	public ArrayDomainExpressionProcessor(final ArrayDomainToolkit<STATE> toolkit) {
		mToolkit = toolkit;
	}

	public Pair<ArrayDomainState<STATE>, Expression> process(final ArrayDomainState<STATE> state,
			final Expression expression) {
		final Term term = mToolkit.getTerm(expression);
		final Map<Term, Term> substitution = new HashMap<>();
		final List<IProgramVarOrConst> auxVars = new ArrayList<>();
		final List<Term> constraints = new ArrayList<>();
		ArrayDomainState<STATE> tmpState = state;
		final Script script = mToolkit.getScript();
		final Term stateTerm = state.getSubTerm();
		// TODO: Replace array (in)equalities
		for (final MultiDimensionalSelect select : MultiDimensionalSelect.extractSelectShallow(term, false)) {
			final Term selectTerm = select.getSelectTerm();
			final Expression array = mToolkit.getExpression(select.getArray());
			final IProgramVar auxVar = mToolkit.createVariable("aux", mToolkit.getType(selectTerm.getSort()));
			auxVars.add(auxVar);
			if (select.getIndex().size() == 1) {
				final Term index = select.getIndex().get(0);
				final Pair<STATE, Segmentation> segmentationPair = tmpState.getSegmentation(array);
				tmpState = tmpState.updateState(segmentationPair.getFirst());
				final Segmentation segmentation = segmentationPair.getSecond();
				final Pair<Integer, Integer> bounds = tmpState.getContainedBoundIndices(segmentation, index);
				final int min = bounds.getFirst();
				final int max = bounds.getSecond();
				final List<Term> disjuncts = new ArrayList<>();
				for (int i = min; i < max; i++) {
					disjuncts.add(mToolkit.connstructEquivalentConstraint(auxVar, segmentation.getValue(i), stateTerm));
				}
				constraints.add(SmtUtils.or(script, disjuncts));
			} else {
				throw new UnsupportedOperationException();
			}
			substitution.put(selectTerm, auxVar.getTermVariable());
		}
		final STATE newSubState = mToolkit.handleAssumptionBySubdomain(tmpState.getSubState().addVariables(auxVars),
				SmtUtils.and(script, constraints));
		final Term newTerm = new Substitution(mToolkit.getManagedScript(), substitution).transform(term);
		return new Pair<>(state.updateState(newSubState), mToolkit.getExpression(newTerm));
	}
}
