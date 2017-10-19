/*
 * Copyright (C) 2017 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TypeSortTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.TemporaryBoogieVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ArrayDomainState<STATE extends IAbstractState<STATE>> implements IAbstractState<ArrayDomainState<STATE>> {
	private final STATE mSubState;
	private final SegmentationMap mSegmentationMap;
	private ArrayDomainToolkit<STATE> mToolkit;
	private Set<IProgramVarOrConst> mVariables;

	private ArrayDomainState(final STATE subState, final SegmentationMap arraySegmentationMap,
			final Set<IProgramVarOrConst> variables, final ArrayDomainToolkit<STATE> toolkit) {
		final TemporaryBoogieVar topValue = toolkit.getTopValue();
		mSubState = subState.containsVariable(topValue) ? subState : subState.addVariable(topValue);
		mSegmentationMap = arraySegmentationMap;
		mToolkit = toolkit;
		mVariables = variables;
	}

	public ArrayDomainState(final STATE subState, final ArrayDomainToolkit<STATE> toolkit) {
		this(subState, new SegmentationMap(), subState.getVariables(), toolkit);
	}

	@Override
	public ArrayDomainState<STATE> addVariable(final IProgramVarOrConst variable) {
		return addVariables(Collections.singleton(variable));
	}

	@Override
	public ArrayDomainState<STATE> removeVariable(final IProgramVarOrConst variable) {
		return removeVariables(Collections.singleton(variable));
	}

	@Override
	public ArrayDomainState<STATE> addVariables(final Collection<IProgramVarOrConst> variables) {
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mVariables);
		final List<IProgramVarOrConst> nonArrayVars = new ArrayList<>();
		for (final IProgramVarOrConst v : variables) {
			newVariables.add(v);
			if (v.getSort().isArraySort()) {
				newSegmentationMap.add(v, mToolkit.getDefaultSegmentation());
			} else {
				nonArrayVars.add(v);
			}
		}
		final STATE newState = mSubState.addVariables(nonArrayVars);
		return new ArrayDomainState<>(newState, newSegmentationMap, newVariables, mToolkit);
	}

	@Override
	public ArrayDomainState<STATE> removeVariables(final Collection<IProgramVarOrConst> variables) {
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mVariables);
		final Set<IProgramVarOrConst> nonArrayVars = new HashSet<>();
		for (final IProgramVarOrConst v : variables) {
			if (!mVariables.contains(v)) {
				throw new UnsupportedOperationException("Unknown variable " + v);
			}
			newVariables.remove(v);
			if (v.getSort().isArraySort()) {
				newSegmentationMap.remove(v);
			} else {
				nonArrayVars.add(v);
			}
		}
		final STATE newState = mSubState.removeVariables(nonArrayVars);
		return new ArrayDomainState<>(newState, newSegmentationMap, newVariables, mToolkit).removeUnusedAuxVars();
	}

	@Override
	public ArrayDomainState<STATE> renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		final Map<IProgramVarOrConst, IProgramVarOrConst> nonArrayVarMap = new HashMap<>();
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mVariables);
		for (final Entry<IProgramVarOrConst, IProgramVarOrConst> entry : old2newVars.entrySet()) {
			final IProgramVarOrConst oldVar = entry.getKey();
			final IProgramVarOrConst newVar = entry.getValue();
			newVariables.remove(oldVar);
			newVariables.add(newVar);
			if (oldVar.getSort().isArraySort()) {
				newSegmentationMap.renameArray(oldVar, newVar);
			} else {
				nonArrayVarMap.put(oldVar, newVar);
			}
		}
		final STATE newState = mSubState.renameVariables(nonArrayVarMap);
		return new ArrayDomainState<>(newState, newSegmentationMap, newVariables, mToolkit);
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mVariables.contains(var);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return mVariables;
	}

	@Override
	public ArrayDomainState<STATE> patch(final ArrayDomainState<STATE> dominator) {
		final STATE newSubState = mSubState.patch(dominator.mSubState);
		final Set<IProgramVarOrConst> oldArrays = mSegmentationMap.getArrays();
		final Set<IProgramVarOrConst> dominatorArrays = dominator.mSegmentationMap.getArrays();
		final Set<IProgramVarOrConst> overwrittenArrays = DataStructureUtils.intersection(oldArrays, dominatorArrays);
		final Set<IProgramVarOrConst> newVariables = DataStructureUtils.union(mVariables, dominator.mVariables);
		final ArrayDomainState<STATE> result =
				new ArrayDomainState<>(newSubState, getSegmentationMap(), newVariables, mToolkit)
						.removeVariables(overwrittenArrays);
		result.mSegmentationMap.addAll(dominator.mSegmentationMap);
		return result.removeUnusedAuxVars();
	}

	public ArrayDomainState<STATE> setSegmentationIntersection(final Segmentation s1, final Segmentation s2,
			final Set<IProgramVarOrConst> arrayEquivalenceClass) {
		STATE newState = mSubState;
		final Script script = mToolkit.getScript();
		final Sort arraySort = arrayEquivalenceClass.iterator().next().getSort();
		final Sort boundSort = TypeUtils.getIndexSort(arraySort);
		final Sort valueSort = TypeUtils.getInnermostArrayValueSort(arraySort);
		final TypeSortTranslator translator = new TypeSortTranslator(script, null);
		final IBoogieType boundType = translator.getType(boundSort);
		final IBoogieType valueType = translator.getType(valueSort);
		final List<IProgramVar> bounds = new ArrayList<>();
		final List<IProgramVar> values = new ArrayList<>();
		final IProgramVar minBound = mToolkit.getMinBound();
		final IProgramVar maxBound = mToolkit.getMaxBound();
		bounds.add(minBound);
		final IProgramVar v0 = mToolkit.createValueVar(valueType);
		values.add(v0);
		final Statement assume =
				createAssume(getEqualities(v0, Arrays.asList(s1.getValue(0), s2.getValue(0)), Operator.LOGICAND));
		newState = mToolkit.handleStatementBySubdomain(newState, assume);
		int idx1 = 1;
		int idx2 = 1;
		while (idx1 < s1.size() || idx2 < s2.size()) {
			final IProgramVar b1 = s1.getBound(idx1);
			final IProgramVar b2 = s2.getBound(idx2);
			final IProgramVarOrConst v1 = s1.getValue(idx1);
			final IProgramVar v2 = s2.getValue(idx2);
			final IProgramVar v1Old = s1.getValue(idx1 - 1);
			final IProgramVar v2Old = s2.getValue(idx2 - 1);
			final Term t1 = getTerm(b1);
			final Term t2 = getTerm(b2);
			final List<Term> constraints = new ArrayList<>();
			if (!b1.equals(maxBound) && !b2.equals(maxBound)
					&& boundConstraintIsTrue(SmtUtils.binaryEquality(script, t1, t2))) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				newState = newState.addVariable(b).addVariable(v);
				constraints.add(getEquality(b, b1));
				constraints.add(getEqualities(v, Arrays.asList(v1, v2), Operator.LOGICAND));
				idx1++;
				idx2++;
			} else if (b2.equals(maxBound) || boundConstraintIsTrue(SmtUtils.leq(script, t1, t2))) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				newState = newState.addVariable(b).addVariable(v);
				constraints.add(getEquality(b, b1));
				constraints.add(getEqualities(v, Arrays.asList(v1, v2Old), Operator.LOGICAND));
				idx1++;
			} else if (b1.equals(maxBound) || boundConstraintIsTrue(SmtUtils.geq(script, t1, t2))) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				newState = newState.addVariable(b).addVariable(v);
				constraints.add(getEquality(b, b2));
				constraints.add(getEqualities(v, Arrays.asList(v1Old, v2), Operator.LOGICAND));
				idx2++;
			} else {
				final IProgramVar bLow = mToolkit.createBoundVar(boundType);
				final IProgramVar bHigh = mToolkit.createBoundVar(boundType);
				final IProgramVar vLow = mToolkit.createValueVar(valueType);
				final IProgramVar vHigh = mToolkit.createValueVar(valueType);
				bounds.add(bLow);
				bounds.add(bHigh);
				values.add(vLow);
				values.add(vHigh);
				newState = newState.addVariables(Arrays.asList(bLow, bHigh, vLow, vHigh));
				// Bound constraints
				constraints.add(SmtUtils.leq(script, getTerm(bLow), getTerm(b1)));
				constraints.add(SmtUtils.leq(script, getTerm(bLow), getTerm(b2)));
				constraints.add(SmtUtils.geq(script, getTerm(bLow), getTerm(s1.getBound(idx1 - 1))));
				constraints.add(SmtUtils.geq(script, getTerm(bLow), getTerm(s2.getBound(idx2 - 1))));
				constraints.add(SmtUtils.geq(script, getTerm(bHigh), getTerm(b1)));
				constraints.add(SmtUtils.geq(script, getTerm(bHigh), getTerm(b2)));
				// TODO: s1.getBound(idx1 + 1) or s2.getBound(idx2 + 1) might return the max-bound!
				constraints.add(SmtUtils.leq(script, getTerm(bHigh), getTerm(s1.getBound(idx1 + 1))));
				constraints.add(SmtUtils.leq(script, getTerm(bHigh), getTerm(s2.getBound(idx2 + 1))));
				// Value constraints
				constraints.add(getEqualities(vLow, Arrays.asList(v1, v1Old), Operator.LOGICOR));
				constraints.add(getEqualities(vLow, Arrays.asList(v2, v2Old), Operator.LOGICOR));
				constraints.add(getEqualities(vHigh, Arrays.asList(v1, v2), Operator.LOGICAND));
				idx1++;
				idx2++;
			}
			final AssumeStatement assume2 = createAssume(SmtUtils.and(script, constraints));
			newState = mToolkit.handleStatementBySubdomain(newState, assume2);
		}
		bounds.add(maxBound);
		final Segmentation segmentation = new Segmentation(bounds, values);
		final SegmentationMap arraySegmentationMap = getSegmentationMap();
		arraySegmentationMap.addEquivalenceClass(arrayEquivalenceClass, segmentation);
		return new ArrayDomainState<>(newState, arraySegmentationMap, mVariables, mToolkit);
	}

	@Override
	public ArrayDomainState<STATE> intersect(final ArrayDomainState<STATE> other) {
		if (isBottom()) {
			return this;
		}
		if (other.isBottom()) {
			return other;
		}
		final ArrayDomainState<STATE> renamedState = other.renameSegmentations(this);
		final Set<IProgramVarOrConst> auxVars1 = mSegmentationMap.getAuxVars();
		final Set<IProgramVarOrConst> auxVars2 = renamedState.mSegmentationMap.getAuxVars();
		final ArrayDomainState<STATE> state1 = addVariables(DataStructureUtils.difference(auxVars2, auxVars1));
		final ArrayDomainState<STATE> state2 =
				renamedState.addVariables(DataStructureUtils.difference(auxVars1, auxVars2));
		final STATE subState = state1.mSubState.intersect(state2.mSubState);
		ArrayDomainState<STATE> result = new ArrayDomainState<>(subState, mToolkit);
		final Set<IProgramVarOrConst> processedArrays = new HashSet<>();
		for (final IProgramVarOrConst v : mSegmentationMap.getArrays()) {
			if (processedArrays.contains(v)) {
				continue;
			}
			final Set<IProgramVarOrConst> equivalenceClass = new HashSet<>();
			final LinkedList<IProgramVarOrConst> queue = new LinkedList<>();
			queue.add(v);
			while (!queue.isEmpty()) {
				final IProgramVarOrConst current = queue.removeFirst();
				if (processedArrays.contains(current)) {
					continue;
				}
				processedArrays.add(current);
				final Set<IProgramVarOrConst> currentEquivalenceClass = new HashSet<>();
				currentEquivalenceClass.addAll(state1.getEqualArrays(current));
				currentEquivalenceClass.addAll(state2.getEqualArrays(current));
				queue.addAll(currentEquivalenceClass);
				equivalenceClass.addAll(currentEquivalenceClass);
			}
			final Set<Segmentation> segmentations = new HashSet<>();
			for (final IProgramVarOrConst eq : equivalenceClass) {
				segmentations.add(state1.getSegmentation(eq));
				segmentations.add(state2.getSegmentation(eq));
			}
			if (segmentations.size() < 2) {
				// If the segmentations are equal, we do not need to change it
				continue;
			}
			final Iterator<Segmentation> iterator = segmentations.iterator();
			result = result.setSegmentationIntersection(iterator.next(), iterator.next(), equivalenceClass);
			while (iterator.hasNext()) {
				result = result.setSegmentationIntersection(result.getSegmentation(v), iterator.next(),
						equivalenceClass);
			}
		}
		return result.removeUnusedAuxVars();
	}

	private ArrayDomainState<STATE> renameSegmentations(final ArrayDomainState<STATE> other) {
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars = new HashMap<>();
		final Set<Segmentation> processedSegmentations = new HashSet<>();
		for (final IProgramVarOrConst array : mSegmentationMap.getArrays()) {
			final Segmentation segmentation = getSegmentation(array);
			if (processedSegmentations.contains(segmentation)) {
				continue;
			}
			processedSegmentations.add(segmentation);
			if (getEqualArrays(array).stream().anyMatch(x -> other.getSegmentation(x).equals(segmentation))) {
				continue;
			}
			newSegmentationMap.put(array, createFreshSegmentationCopy(segmentation, old2newVars));
		}
		final STATE newSubState = mSubState.renameVariables(old2newVars);
		return new ArrayDomainState<>(newSubState, newSegmentationMap, mVariables, mToolkit);
	}

	private Segmentation createFreshSegmentationCopy(final Segmentation segmentation,
			final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		final List<IProgramVar> newBounds = new ArrayList<>();
		final List<IProgramVar> newValues = new ArrayList<>();
		newBounds.add(mToolkit.getMinBound());
		newValues.add(createFreshVar(segmentation.getValue(0), old2newVars, true));
		for (int i = 1; i < segmentation.size(); i++) {
			newBounds.add(createFreshVar(segmentation.getBound(i), old2newVars, false));
			newValues.add(createFreshVar(segmentation.getValue(i), old2newVars, true));
		}
		newBounds.add(mToolkit.getMaxBound());
		return new Segmentation(newBounds, newValues);
	}

	private IProgramVar createFreshVar(final IProgramVar oldVar,
			final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars, final boolean isValue) {
		if (!old2newVars.containsKey(oldVar)) {
			final IBoogieType type = new TypeSortTranslator(mToolkit.getScript(), null).getType(oldVar.getSort());
			old2newVars.put(oldVar, isValue ? mToolkit.createValueVar(type) : mToolkit.createBoundVar(type));
		}
		return (IProgramVar) old2newVars.get(oldVar);
	}

	@Override
	public ArrayDomainState<STATE> union(final ArrayDomainState<STATE> other) {
		if (isBottom()) {
			return other;
		}
		if (other.isBottom()) {
			return this;
		}
		// TODO: Rename variables first
		/*
		 * final STATE state = operator.apply(mSubState, other.mSubState); ArrayDomainState<STATE> result =
		 * updateState(state, mSegmentationMap); final Set<IProgramVarOrConst> processedArrays = new HashSet<>(); for
		 * (final IProgramVarOrConst v : mSegmentationMap.getArrays()) { if (processedArrays.contains(v)) { continue; }
		 * processedArrays.add(v); final Set<IProgramVarOrConst> equivalenceClass = new HashSet<>();
		 * equivalenceClass.addAll(getEqualArrays(v)); equivalenceClass.retainAll(other.getEqualArrays(v));
		 * processedArrays.addAll(equivalenceClass); result = result.setSegmentationUnion(getSegmentation(v),
		 * other.getSegmentation(v), equivalenceClass); } return result.removeUnusedAuxVars();
		 */
		// TODO:
		return null;
	}

	public ArrayDomainState<STATE> setSegmentationUnion(final Segmentation s1, final Segmentation s2,
			final Set<IProgramVarOrConst> equivalenceClass) {
		// TODO Auto-generated method stub
		return null;
	}

	public ArrayDomainState<STATE> applyWidening(final ArrayDomainState<STATE> other) {
		// TODO: Implement proper widenning!
		return union(other);
	}

	@Override
	public boolean isEmpty() {
		return mSubState.isEmpty() && mSegmentationMap.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return mSubState.isBottom();
	}

	@Override
	public boolean isEqualTo(final ArrayDomainState<STATE> other) {
		return isSubsetOf(other) == SubsetResult.EQUAL;
	}

	@Override
	public SubsetResult isSubsetOf(final ArrayDomainState<STATE> other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ArrayDomainState<STATE> compact() {
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		final STATE newSubState = mSubState.compact();
		final Segmentation defaultSegmentation = mToolkit.getDefaultSegmentation();
		for (final IProgramVarOrConst a : mSegmentationMap.getArrays()) {
			if (mSegmentationMap.getEquivalenceClass(a).size() == 1
					&& mSegmentationMap.getSegmentation(a).equals(defaultSegmentation)) {
				newSegmentationMap.remove(a);
			}
		}
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(newSubState.getVariables());
		newVariables.addAll(newSegmentationMap.getArrays());
		newVariables.retainAll(mVariables);
		return new ArrayDomainState<>(newSubState, newSegmentationMap, newVariables, mToolkit);
	}

	@Override
	public Term getTerm(final Script script) {
		if (isBottom()) {
			return script.term("false");
		}
		final Term term = mSubState.getTerm(script);
		final Function<IProgramVarOrConst, TermVariable> termVar = x -> ((IProgramVar) x).getTermVariable();
		final Set<TermVariable> bounds =
				mSegmentationMap.getBoundVars().stream().map(termVar).collect(Collectors.toSet());
		final Set<TermVariable> values =
				mSegmentationMap.getValueVars().stream().map(termVar).collect(Collectors.toSet());
		final Term valueTerm = SmtUtils.filterFormula(term, values, script, true);
		final Term nonValueTerm = SmtUtils.filterFormula(term, values, script, false);
		final Term arrayTerm = mSegmentationMap.getTerm(mToolkit.getManagedScript(), valueTerm);
		final Term conjunction = Util.and(script, nonValueTerm, arrayTerm);
		final Set<TermVariable> auxVars = DataStructureUtils.union(bounds, values);
		// TODO: Simplify and apply QE
		return SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, auxVars, conjunction);
	}

	@Override
	public String toString() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(mSegmentationMap);
		stringBuilder.append("\n\nSubstate: ").append(mSubState);
		return stringBuilder.toString();
	}

	@Override
	public String toLogString() {
		return toString();
	}

	private Segmentation getSegmentation(final IProgramVarOrConst array) {
		return mSegmentationMap.getSegmentation(array);
	}

	// TODO: Since new aux-vars can be created, we have to return a new state aswell!
	public Segmentation getSegmentation(final Expression array) {
		Segmentation result = null;
		if (array instanceof IdentifierExpression) {
			final IProgramVarOrConst arrayVar = mToolkit.getBoogieVar((IdentifierExpression) array);
			result = getSegmentation(arrayVar);
		}
		// TODO: Handle other cases, such as a[i:=v]
		return result == null ? mToolkit.getDefaultSegmentation() : result;
	}

	private Set<IProgramVarOrConst> getEqualArrays(final IProgramVarOrConst array) {
		return mSegmentationMap.getEquivalenceClass(array);
	}

	private boolean boundConstraintIsTrue(final Term term) {
		return mSubState.evaluate(mToolkit.getScript(), term) == EvalResult.TRUE;
	}

	private AssumeStatement createAssume(final Term term) {
		return new AssumeStatement(null, mToolkit.getExpression(term));
	}

	private static Term getTerm(final IProgramVarOrConst var) {
		return NonrelationalTermUtils.getTermVar(var);
	}

	private Term getEqualities(final IProgramVarOrConst var, final List<IProgramVarOrConst> others, final Operator op) {
		assert op == Operator.LOGICAND || op == Operator.LOGICOR;
		final List<Term> xjuncts = new ArrayList<>();
		for (final IProgramVarOrConst v : others) {
			xjuncts.add(getEquality(var, v));
		}
		return op == Operator.LOGICOR ? SmtUtils.or(mToolkit.getScript(), xjuncts)
				: SmtUtils.and(mToolkit.getScript(), xjuncts);
	}

	private Term getEquality(final IProgramVarOrConst var1, final IProgramVarOrConst var2) {
		return SmtUtils.binaryEquality(mToolkit.getScript(), getTerm(var1), getTerm(var1));
	}

	@Override
	public EvalResult evaluate(final Script script, final Term term) {
		// TODO: Implement (low priority, should be never called)
		// Idea: Replace all select-terms by fresh aux-vars that are added to boundState and valueState
		// and evaluate on these states
		return EvalResult.UNKNOWN;
	}

	public ArrayDomainState<STATE> updateState(final STATE newSubState, final SegmentationMap newSegmentationMap) {
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(newSubState.getVariables());
		newVariables.addAll(newSegmentationMap.getArrays());
		newVariables.removeAll(newSegmentationMap.getAuxVars());
		return new ArrayDomainState<>(newSubState, newSegmentationMap, newVariables, mToolkit);
	}

	public ArrayDomainState<STATE> updateState(final STATE newSubState) {
		return new ArrayDomainState<>(newSubState, getSegmentationMap(), mVariables, mToolkit);
	}

	public STATE getSubState() {
		return mSubState;
	}

	public SegmentationMap getSegmentationMap() {
		return new SegmentationMap(mSegmentationMap);
	}

	public Pair<Integer, Integer> getContainedBoundIndices(final Expression array, final Expression index) {
		final Segmentation segmentation = getSegmentation(array);
		final Term indexTerm = mToolkit.getTerm(index);
		int min = segmentation.size() - 1;
		final Script script = mToolkit.getScript();
		for (int i = 1; i < segmentation.size(); i++) {
			final Term bound = getTerm(segmentation.getBound(i));
			final Term term = SmtUtils.leq(script, bound, indexTerm);
			if (!boundConstraintIsTrue(term)) {
				min = i - 1;
				break;
			}
		}
		int max = min + 1;
		for (int i = segmentation.size() - 1; i > min; i--) {
			final Term bound = getTerm(segmentation.getBound(i));
			final Term term = SmtUtils.less(script, indexTerm, bound);
			if (!boundConstraintIsTrue(term)) {
				max = i + 1;
				break;
			}
		}
		return new Pair<>(min, max);
	}

	public Set<IProgramVarOrConst> getUnusedAuxVars() {
		final Set<IProgramVarOrConst> vars = mSubState.getVariables();
		vars.removeAll(mVariables);
		vars.removeAll(mSegmentationMap.getAuxVars());
		return vars;
	}

	public ArrayDomainState<STATE> removeUnusedAuxVars() {
		final STATE newSubState = mSubState.removeVariables(getUnusedAuxVars());
		return new ArrayDomainState<>(newSubState, mSegmentationMap, mVariables, mToolkit);
	}

	// TODO
	public ArrayDomainState<STATE> simplifySegmentation(final IProgramVarOrConst array) {
		final Script script = mToolkit.getScript();
		final Term term = mSubState.getTerm(script);
		final Segmentation segmentation = getSegmentation(array);
		int current = 0;
		int next = 1;
		final List<IProgramVar> newBounds = new ArrayList<>();
		final List<IProgramVar> newValues = new ArrayList<>();
		// TODO: Correct exit condition!
		while (current < segmentation.size()) {
			final TermVariable currentValueVar = segmentation.getValue(current).getTermVariable();
			final TermVariable nextValueVar = segmentation.getValue(next).getTermVariable();
			final Term currentTerm =
					SmtUtils.filterFormula(term, Collections.singleton(currentValueVar), script, true);
			final Term nextTerm = SmtUtils.filterFormula(term, Collections.singleton(nextValueVar), script, true);
			final Substitution substitution = new Substitution(mToolkit.getManagedScript(),
					Collections.singletonMap(nextValueVar, currentValueVar));
			final Term currentSubstitutedTerm = substitution.transform(currentTerm);
			final Term nextSubstitutedTerm = substitution.transform(nextTerm);
			if (SmtUtils.areFormulasEquivalent(currentSubstitutedTerm, nextSubstitutedTerm, script)) {
				next++;
			} else {
				newBounds.add(segmentation.getBound(current));
				newValues.add(segmentation.getValue(current));
				current = next++;
			}
		}
		newBounds.add(mToolkit.getMaxBound());
		final Segmentation newSegmentation = new Segmentation(newBounds, newValues);
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		newSegmentationMap.put(array, newSegmentation);
		return new ArrayDomainState<>(mSubState, newSegmentationMap, mVariables, mToolkit);
	}
}
