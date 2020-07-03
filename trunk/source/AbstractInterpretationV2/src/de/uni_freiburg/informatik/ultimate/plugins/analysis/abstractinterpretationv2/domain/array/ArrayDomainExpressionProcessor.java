package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ArrayDomainExpressionProcessor<STATE extends IAbstractState<STATE>> {
	private final ArrayDomainToolkit<STATE> mToolkit;

	public ArrayDomainExpressionProcessor(final ArrayDomainToolkit<STATE> toolkit) {
		mToolkit = toolkit;
	}

	public Pair<ArrayDomainState<STATE>, Expression> processExpression(final ArrayDomainState<STATE> state,
			final Expression expression) {
		final Pair<ArrayDomainState<STATE>, Term> termResult = processTerm(state, mToolkit.getTerm(expression));
		return new Pair<>(termResult.getFirst(), mToolkit.getExpression(termResult.getSecond()));
	}

	private Pair<ArrayDomainState<STATE>, Term> processTerm(final ArrayDomainState<STATE> state, final Term term) {
		final Map<Term, Term> substitution = new HashMap<>();
		final List<IProgramVarOrConst> auxVars = new ArrayList<>();
		final List<Term> constraints = new ArrayList<>();
		ArrayDomainState<STATE> tmpState = state;
		final Script script = mToolkit.getScript();
		for (final MultiDimensionalSelect select : MultiDimensionalSelect.extractSelectShallow(term, true)) {
			final Term selectTerm = select.getSelectTerm();
			Term currentTerm = select.getArray();
			for (final Term index : select.getIndex()) {
				final Pair<ArrayDomainState<STATE>, Segmentation> segmentationPair =
						tmpState.getSegmentation(mToolkit.getExpression(currentTerm));
				tmpState = segmentationPair.getFirst();
				final Segmentation segmentation = segmentationPair.getSecond();
				final Pair<Integer, Integer> bounds = tmpState.getContainedBoundIndices(segmentation, index);
				final int min = bounds.getFirst();
				final int max = bounds.getSecond();
				final IProgramVar auxVar = mToolkit.createAuxVar(TypeUtils.getValueSort(currentTerm.getSort()));
				final Sort sort = auxVar.getSort();
				if (sort.isArraySort()) {
					final List<Segmentation> segmentations = new ArrayList<>();
					for (int i = min; i < max; i++) {
						segmentations.add(tmpState.getSegmentation(segmentation.getValue(i)));
					}
					final Pair<Segmentation, ArrayDomainState<STATE>> pair =
							tmpState.unionSegmentations(segmentations, sort);
					final SegmentationMap newSegmentationMap = pair.getSecond().getSegmentationMap();
					newSegmentationMap.put(auxVar, pair.getFirst());
					tmpState = pair.getSecond().updateState(newSegmentationMap);
				} else {
					auxVars.add(auxVar);
					final List<Term> disjuncts = new ArrayList<>();
					for (int i = min; i < max; i++) {
						disjuncts.add(mToolkit.connstructEquivalentConstraint(auxVar, segmentation.getValue(i),
								tmpState.getSubTerm()));
					}
					constraints.add(SmtUtils.or(script, disjuncts));
				}
				currentTerm = auxVar.getTermVariable();
			}
			substitution.put(selectTerm, currentTerm);
		}
		final STATE newSubState = mToolkit.handleAssumptionBySubdomain(tmpState.getSubState().addVariables(auxVars),
				SmtUtils.and(script, constraints));
		final Term newTerm = new Substitution(mToolkit.getManagedScript(), substitution).transform(term);
		return new Pair<>(tmpState.updateState(newSubState), newTerm);
	}

	public ArrayDomainState<STATE> processAssume(final ArrayDomainState<STATE> state, final Expression assumption) {
		final Term term = mToolkit.getTerm(assumption);
		if (SmtUtils.isArrayFree(term)) {
			return state.updateState(mToolkit.handleAssumptionBySubdomain(state.getSubState(), term));
		}
		ArrayDomainState<STATE> returnState = state;
		final Term cnf = SmtUtils.toCnf(mToolkit.getServices(), mToolkit.getManagedScript(), term,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		for (final Term t : SmtUtils.getConjuncts(cnf)) {
			if (returnState.isBottom()) {
				break;
			}
			returnState = processAssumeTerm(returnState, t);
		}
		return returnState;
	}

	private ArrayDomainState<STATE> processAssumeTerm(final ArrayDomainState<STATE> state, final Term assumption) {
		assert !SmtUtils.isFunctionApplication(assumption, "and");
		final Script script = mToolkit.getScript();
		if (SmtUtils.isFunctionApplication(assumption, "or")) {
			ArrayDomainState<STATE> returnState = mToolkit.createBottomState();
			final List<Term> arrayFreeDisjuncts = new ArrayList<>();
			for (final Term t : ((ApplicationTerm) assumption).getParameters()) {
				if (SmtUtils.isArrayFree(t)) {
					arrayFreeDisjuncts.add(t);
				} else {
					final ArrayDomainState<STATE> postState = processAssumeTerm(state, t).simplify();
					returnState = returnState.union(postState);
				}
			}
			if (arrayFreeDisjuncts.isEmpty()) {
				return returnState;
			}
			final ArrayDomainState<STATE> postState = state.updateState(
					mToolkit.handleAssumptionBySubdomain(state.getSubState(), SmtUtils.or(script, arrayFreeDisjuncts)));
			return returnState.union(postState);
		}
		// Handle array-equalities
		if (SmtUtils.isFunctionApplication(assumption, "=")) {
			final Term[] params = ((ApplicationTerm) assumption).getParameters();
			assert params.length == 2;
			final Sort sort = params[0].getSort();
			if (sort.isArraySort()) {
				final Expression left = mToolkit.getExpression(params[0]);
				final Expression right = mToolkit.getExpression(params[1]);
				final SegmentationMap segmentationMap = state.getSegmentationMap();
				SegmentationMap newSegmentationMap;
				if (left instanceof IdentifierExpression && right instanceof IdentifierExpression) {
					final IProgramVarOrConst leftVar = mToolkit.getBoogieVar((IdentifierExpression) left);
					final IProgramVarOrConst rightVar = mToolkit.getBoogieVar((IdentifierExpression) right);
					final Segmentation leftSegmentation = segmentationMap.getSegmentation(leftVar);
					final Segmentation rightSegmentation = segmentationMap.getSegmentation(rightVar);
					final Pair<Segmentation, ArrayDomainState<STATE>> intersectionResult =
							state.intersectSegmentations(leftSegmentation, rightSegmentation, sort);
					newSegmentationMap = intersectionResult.getSecond().getSegmentationMap();
					newSegmentationMap.union(leftVar, rightVar, intersectionResult.getFirst());
					return intersectionResult.getSecond().updateState(newSegmentationMap);
				}
				if (left instanceof IdentifierExpression) {
					final IProgramVarOrConst leftVar = mToolkit.getBoogieVar((IdentifierExpression) left);
					final Segmentation leftSegmentation = segmentationMap.getSegmentation(leftVar);
					final Pair<ArrayDomainState<STATE>, Segmentation> rightPair = state.getSegmentation(right);
					final Segmentation rightSegmentation = rightPair.getSecond();
					final Pair<Segmentation, ArrayDomainState<STATE>> intersectionResult =
							rightPair.getFirst().intersectSegmentations(leftSegmentation, rightSegmentation, sort);
					newSegmentationMap = intersectionResult.getSecond().getSegmentationMap();
					newSegmentationMap.put(leftVar, intersectionResult.getFirst());
					return intersectionResult.getSecond().updateState(newSegmentationMap);
				}
				if (right instanceof IdentifierExpression) {
					final Pair<ArrayDomainState<STATE>, Segmentation> leftPair = state.getSegmentation(left);
					final Segmentation leftSegmentation = leftPair.getSecond();
					final IProgramVarOrConst rightVar = mToolkit.getBoogieVar((IdentifierExpression) right);
					final Segmentation rightSegmentation = segmentationMap.getSegmentation(rightVar);
					final Pair<Segmentation, ArrayDomainState<STATE>> intersectionResult =
							leftPair.getFirst().intersectSegmentations(leftSegmentation, rightSegmentation, sort);
					newSegmentationMap = intersectionResult.getSecond().getSegmentationMap();
					newSegmentationMap.put(rightVar, intersectionResult.getFirst());
					return intersectionResult.getSecond().updateState(newSegmentationMap);
				}
				return state;
			}
		}
		// Handle array-inequalities
		if (isInvalidArrayInequality(state, assumption)) {
			return mToolkit.createBottomState();
		}
		// Handle array-reads
		final List<MultiDimensionalSelect> selects = MultiDimensionalSelect.extractSelectShallow(assumption, true);
		if (selects.isEmpty()) {
			final STATE newSubState = mToolkit.handleAssumptionBySubdomain(state.getSubState(), assumption);
			return state.updateState(newSubState);
		}
		final List<Term> constraints = new ArrayList<>();
		final Map<Term, Term> substitution = new HashMap<>();
		ArrayDomainState<STATE> newState = state;
		for (final MultiDimensionalSelect select : selects) {
			final Expression arrayExpr = mToolkit.getExpression(select.getArray());
			if (!(arrayExpr instanceof IdentifierExpression)) {
				continue;
			}
			final Term selectTerm = select.getSelectTerm();
			final Pair<ArrayDomainState<STATE>, Term> oldValueResult = processTerm(newState, selectTerm);
			final Term oldValue = oldValueResult.getSecond();
			final IProgramVar auxVar = mToolkit.createAuxVar(selectTerm.getSort());
			final TermVariable auxVarTv = auxVar.getTermVariable();
			substitution.put(selectTerm, auxVarTv);
			constraints.add(SmtUtils.binaryEquality(script, auxVarTv, oldValue));
			final Expression store = mToolkit.getExpression(
					SmtUtils.multiDimensionalStore(script, select.getArray(), select.getIndex(), auxVarTv));
			final ArrayDomainState<STATE> tmpState = oldValueResult.getFirst().addAuxVar(auxVar);
			final Pair<ArrayDomainState<STATE>, Segmentation> segmentationPair = tmpState.getSegmentation(store);
			newState = segmentationPair.getFirst();
			final IProgramVarOrConst arrayVar = mToolkit.getBoogieVar((IdentifierExpression) arrayExpr);
			final SegmentationMap newSegmentationMap = newState.getSegmentationMap();
			newSegmentationMap.put(arrayVar, segmentationPair.getSecond());
			newState = newState.updateState(newSegmentationMap);
		}
		if (substitution.isEmpty()) {
			constraints.add(assumption);
		} else {
			constraints.add(new Substitution(mToolkit.getManagedScript(), substitution).transform(assumption));
		}
		final STATE newSubState =
				mToolkit.handleAssumptionBySubdomain(newState.getSubState(), SmtUtils.and(script, constraints));
		return newState.updateState(newSubState);
	}

	private boolean isInvalidArrayInequality(final ArrayDomainState<STATE> state, final Term assumption) {
		if (!SmtUtils.isFunctionApplication(assumption, "not")) {
			return false;
		}
		final Term subTerm = ((ApplicationTerm) assumption).getParameters()[0];
		if (!SmtUtils.isFunctionApplication(subTerm, "=")) {
			return false;
		}
		final Term[] params = ((ApplicationTerm) subTerm).getParameters();
		assert params.length == 2;
		if (!params[0].getSort().isArraySort()) {
			return false;
		}
		final Expression left = mToolkit.getExpression(params[0]);
		final Expression right = mToolkit.getExpression(params[1]);
		if (!(left instanceof IdentifierExpression && right instanceof IdentifierExpression)) {
			return false;
		}
		final IProgramVarOrConst leftVar = mToolkit.getBoogieVar((IdentifierExpression) left);
		final IProgramVarOrConst rightVar = mToolkit.getBoogieVar((IdentifierExpression) right);
		return state.getSegmentationMap().getEquivalenceClass(leftVar).contains(rightVar);
	}
}
