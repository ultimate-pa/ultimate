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

import java.security.InvalidParameterException;
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
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ArrayDomainState<STATE extends IAbstractState<STATE>> implements IAbstractState<ArrayDomainState<STATE>> {
	private final STATE mSubState;
	private final SegmentationMap mSegmentationMap;
	private final ArrayDomainToolkit<STATE> mToolkit;
	private final Set<IProgramVarOrConst> mVariables;
	private Term mCachedTerm;
	private EquivalenceFinder mEquivalenceFinder;

	private ArrayDomainState(final STATE subState, final SegmentationMap segmentationMap,
			final Set<IProgramVarOrConst> variables, final ArrayDomainToolkit<STATE> toolkit) {
		mSubState = subState;
		mSegmentationMap = segmentationMap;
		mToolkit = toolkit;
		mVariables = variables;
	}

	public ArrayDomainState(final STATE subState, final Set<IProgramVarOrConst> variables,
			final ArrayDomainToolkit<STATE> toolkit) {
		this(subState, new SegmentationMap(), variables, toolkit);
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
			final Sort sort = v.getSort();
			if (sort.isArraySort()) {
				final IBoogieType valueType = mToolkit.getType(TypeUtils.getValueSort(sort));
				final Pair<IProgramVar, Segmentation> pair = mToolkit.createTopSegmentation(valueType);
				nonArrayVars.add(pair.getFirst());
				newSegmentationMap.add(v, pair.getSecond());
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

	private ArrayDomainState<STATE> setSegmentationIntersection(final Segmentation s1, final Segmentation s2,
			final Set<IProgramVarOrConst> arrayEquivalenceClass) {
		final Script script = mToolkit.getScript();
		final Sort arraySort = arrayEquivalenceClass.iterator().next().getSort();
		final Sort boundSort = TypeUtils.getIndexSort(arraySort);
		final Sort valueSort = TypeUtils.getInnermostArrayValueSort(arraySort);
		final IBoogieType boundType = mToolkit.getType(boundSort);
		final IBoogieType valueType = mToolkit.getType(valueSort);
		final List<IProgramVar> bounds = new ArrayList<>();
		final List<IProgramVar> values = new ArrayList<>();
		final IProgramVar minBound = mToolkit.getMinBound();
		final IProgramVar maxBound = mToolkit.getMaxBound();
		bounds.add(minBound);
		final IProgramVar v0 = mToolkit.createValueVar(valueType);
		values.add(v0);
		final List<Term> constraints = new ArrayList<>();
		constraints.add(
				connstructEquivalentConstraints(v0, Arrays.asList(s1.getValue(0), s2.getValue(0)), Operator.LOGICAND));
		int idx1 = 1;
		int idx2 = 1;
		while (idx1 < s1.size() || idx2 < s2.size()) {
			final IProgramVar b1 = s1.getBound(idx1);
			final IProgramVar b2 = s2.getBound(idx2);
			final IProgramVar v1 = s1.getValue(idx1);
			final IProgramVar v2 = s2.getValue(idx2);
			final IProgramVar v1Old = s1.getValue(idx1 - 1);
			final IProgramVar v2Old = s2.getValue(idx2 - 1);
			final Term t1 = b1.getTermVariable();
			final Term t2 = b2.getTermVariable();
			if (!b1.equals(maxBound) && !b2.equals(maxBound)
					&& mSubState.evaluate(script, SmtUtils.binaryEquality(script, t1, t2)) == EvalResult.TRUE) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				constraints.add(connstructEquivalentConstraint(b, b1));
				constraints.add(connstructEquivalentConstraints(v, Arrays.asList(v1, v2), Operator.LOGICAND));
				idx1++;
				idx2++;
			} else if (b2.equals(maxBound)
					|| mSubState.evaluate(script, SmtUtils.leq(script, t1, t2)) == EvalResult.TRUE) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				constraints.add(connstructEquivalentConstraint(b, b1));
				constraints.add(connstructEquivalentConstraints(v, Arrays.asList(v1, v2Old), Operator.LOGICAND));
				idx1++;
			} else if (b1.equals(maxBound)
					|| mSubState.evaluate(script, SmtUtils.geq(script, t1, t2)) == EvalResult.TRUE) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				constraints.add(connstructEquivalentConstraint(b, b2));
				constraints.add(connstructEquivalentConstraints(v, Arrays.asList(v1Old, v2), Operator.LOGICAND));
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
				// Bound constraints
				constraints.add(SmtUtils.leq(script, NonrelationalTermUtils.getTermVar(bLow),
						NonrelationalTermUtils.getTermVar(b1)));
				constraints.add(SmtUtils.leq(script, NonrelationalTermUtils.getTermVar(bLow),
						NonrelationalTermUtils.getTermVar(b2)));
				constraints.add(SmtUtils.geq(script, NonrelationalTermUtils.getTermVar(bLow),
						NonrelationalTermUtils.getTermVar(s1.getBound(idx1 - 1))));
				constraints.add(SmtUtils.geq(script, NonrelationalTermUtils.getTermVar(bLow),
						NonrelationalTermUtils.getTermVar(s2.getBound(idx2 - 1))));
				constraints.add(SmtUtils.geq(script, NonrelationalTermUtils.getTermVar(bHigh),
						NonrelationalTermUtils.getTermVar(b1)));
				constraints.add(SmtUtils.geq(script, NonrelationalTermUtils.getTermVar(bHigh),
						NonrelationalTermUtils.getTermVar(b2)));
				if (idx1 + 1 < s1.size()) {
					constraints.add(SmtUtils.leq(script, NonrelationalTermUtils.getTermVar(bHigh),
							NonrelationalTermUtils.getTermVar(s1.getBound(idx1 + 1))));
				}
				if (idx2 + 1 < s2.size()) {
					constraints.add(SmtUtils.leq(script, NonrelationalTermUtils.getTermVar(bHigh),
							NonrelationalTermUtils.getTermVar(s2.getBound(idx2 + 1))));
				}
				// Value constraints
				constraints.add(connstructEquivalentConstraints(vLow, Arrays.asList(v1, v1Old), Operator.LOGICOR));
				constraints.add(connstructEquivalentConstraints(vLow, Arrays.asList(v2, v2Old), Operator.LOGICOR));
				constraints.add(connstructEquivalentConstraints(vHigh, Arrays.asList(v1, v2), Operator.LOGICAND));
				idx1++;
				idx2++;
			}
		}
		bounds.add(maxBound);
		mSegmentationMap.addEquivalenceClass(arrayEquivalenceClass, new Segmentation(bounds, values));
		final Set<IProgramVarOrConst> newVars = new HashSet<>();
		newVars.addAll(bounds);
		newVars.remove(minBound);
		newVars.remove(maxBound);
		newVars.addAll(values);
		final STATE newState = mToolkit.handleAssumptionBySubdomain(mSubState.addVariables(newVars),
				SmtUtils.and(script, constraints));
		return updateState(newState);
	}

	// TODO: Use unification
	@Override
	public ArrayDomainState<STATE> intersect(final ArrayDomainState<STATE> other) {
		if (isBottom()) {
			return this;
		}
		if (other.isBottom()) {
			return other;
		}
		final ArrayDomainState<STATE> otherState = other.renameSegmentations(this, true);
		final Set<IProgramVarOrConst> auxVars1 = new HashSet<>(mSegmentationMap.getAuxVars());
		final Set<IProgramVarOrConst> auxVars2 = new HashSet<>(otherState.mSegmentationMap.getAuxVars());
		final STATE state1 = mSubState.addVariables(DataStructureUtils.difference(auxVars2, auxVars1));
		final STATE state2 = otherState.mSubState.addVariables(DataStructureUtils.difference(auxVars1, auxVars2));
		final STATE subState = state1.intersect(state2);
		ArrayDomainState<STATE> result = new ArrayDomainState<>(subState, mVariables, mToolkit);
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
				currentEquivalenceClass.addAll(getEqualArrays(current));
				currentEquivalenceClass.addAll(otherState.getEqualArrays(current));
				queue.addAll(currentEquivalenceClass);
				equivalenceClass.addAll(currentEquivalenceClass);
			}
			final Set<Segmentation> segmentations = new HashSet<>();
			for (final IProgramVarOrConst eq : equivalenceClass) {
				segmentations.add(mSegmentationMap.getSegmentation(eq));
				segmentations.add(otherState.mSegmentationMap.getSegmentation(eq));
			}
			final Iterator<Segmentation> iterator = segmentations.iterator();
			final Segmentation firstSegmentation = iterator.next();
			if (!iterator.hasNext()) {
				// If the segmentations are equal, we can directly set it
				result.mSegmentationMap.add(v, firstSegmentation);
				continue;
			}
			result = result.setSegmentationIntersection(firstSegmentation, iterator.next(), equivalenceClass);
			while (iterator.hasNext()) {
				result = result.setSegmentationIntersection(result.mSegmentationMap.getSegmentation(v), iterator.next(),
						equivalenceClass);
			}
		}
		return result.simplify();
	}

	private ArrayDomainState<STATE> renameSegmentations(final ArrayDomainState<STATE> other,
			final boolean tryToKeepOld) {
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars = new HashMap<>();
		final Set<Segmentation> processedSegmentations = new HashSet<>();
		for (final IProgramVarOrConst array : mSegmentationMap.getArrays()) {
			final Segmentation segmentation = mSegmentationMap.getSegmentation(array);
			if (processedSegmentations.contains(segmentation)) {
				continue;
			}
			processedSegmentations.add(segmentation);
			if (tryToKeepOld && getEqualArrays(array).stream()
					.anyMatch(x -> other.mSegmentationMap.getSegmentation(x).equals(segmentation))) {
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
			final IBoogieType type = mToolkit.getType(oldVar.getSort());
			old2newVars.put(oldVar, isValue ? mToolkit.createValueVar(type) : mToolkit.createBoundVar(type));
		}
		return (IProgramVar) old2newVars.get(oldVar);
	}

	private UnificationResult<STATE> unify(final ArrayDomainState<STATE> otherState, final Segmentation segmentation,
			final Segmentation otherSegmentation) {
		final Script script = mToolkit.getScript();
		final Set<TermVariable> thisBounds = getTermVars(segmentation.getBounds());
		final Set<TermVariable> otherBounds = getTermVars(otherSegmentation.getBounds());
		final EquivalenceFinder eqThis = getEquivalenceFinder();
		final EquivalenceFinder eqOther = otherState.getEquivalenceFinder();
		final UnionFind<Term> eqClassesThis = eqThis.getEquivalences(new HashSet<>(thisBounds));
		final UnionFind<Term> eqClassesOther = eqOther.getEquivalences(new HashSet<>(otherBounds));
		final Set<TermVariable> excludedVars = new HashSet<>();
		excludedVars.addAll(thisBounds);
		excludedVars.addAll(otherBounds);
		excludedVars.addAll(getTermVars(segmentation.getValues()));
		excludedVars.addAll(getTermVars(otherSegmentation.getValues()));
		final List<Set<Term>> boundsThisOld =
				transformSegmentation(eqClassesThis, segmentation, Collections.emptySet(), false).getFirst();
		final List<Set<Term>> boundsOtherOld =
				transformSegmentation(eqClassesOther, otherSegmentation, Collections.emptySet(), false).getFirst();
		final Set<Term> allBounds = unionSets(boundsThisOld);
		allBounds.addAll(unionSets(boundsOtherOld));
		final UnionFind<Term> eqClassesThisExtended = eqThis.getEquivalences(allBounds);
		final UnionFind<Term> eqClassesOtherExtended = eqOther.getEquivalences(allBounds);
		final Pair<List<Set<Term>>, List<IProgramVar>> transformedThis =
				transformSegmentation(eqClassesThisExtended, segmentation, excludedVars, true);
		final Pair<List<Set<Term>>, List<IProgramVar>> transformedOther =
				otherState.transformSegmentation(eqClassesOtherExtended, otherSegmentation, excludedVars, true);
		final List<Set<Term>> boundsThis = transformedThis.getFirst();
		final List<Set<Term>> boundsOther = transformedOther.getFirst();
		final List<IProgramVar> valuesThis = transformedThis.getSecond();
		final List<IProgramVar> valuesOther = transformedOther.getSecond();
		final Set<Term> boundsThisTodo = unionSets(boundsThis);
		final Set<Term> boundsOtherTodo = unionSets(boundsOther);
		final List<Term> constraintsThis = new ArrayList<>();
		final List<Term> constraintsOther = new ArrayList<>();
		// Here unification starts
		final List<Set<Term>> newBounds = new ArrayList<>();
		final List<IProgramVar> newValuesThis = new ArrayList<>();
		final List<IProgramVar> newValuesOther = new ArrayList<>();
		final List<IProgramVarOrConst> removedValuesThis = new ArrayList<>();
		final List<IProgramVarOrConst> removedValuesOther = new ArrayList<>();
		final IProgramVar thisValue0 = valuesThis.get(0);
		final IProgramVar otherValue0 = valuesOther.get(0);
		final IBoogieType valueType = mToolkit.getType(thisValue0.getSort());
		final IProgramVar newValue0 = mToolkit.createValueVar(valueType);
		newValuesThis.add(newValue0);
		newValuesOther.add(newValue0);
		constraintsThis.add(connstructEquivalentConstraint(newValue0, thisValue0));
		constraintsOther.add(otherState.connstructEquivalentConstraint(newValue0, otherValue0));
		int idxThis = 1;
		int idxOther = 1;
		while (idxThis < valuesThis.size() && idxOther < valuesOther.size()) {
			final IProgramVar thisValue = valuesThis.get(idxThis);
			final IProgramVar otherValue = valuesOther.get(idxOther);
			final Set<Term> eqClassThis = boundsThis.get(idxThis);
			final Set<Term> eqClassOther = boundsOther.get(idxOther);
			boundsThisTodo.removeAll(eqClassThis);
			boundsOtherTodo.removeAll(eqClassOther);
			final Set<Term> thisExclusive = DataStructureUtils.difference(eqClassThis, eqClassOther);
			final Set<Term> otherExclusive = DataStructureUtils.difference(eqClassOther, eqClassThis);
			final IProgramVar newValue = mToolkit.createValueVar(valueType);
			if (otherExclusive.isEmpty()) {
				// case 2
				newBounds.add(eqClassOther);
				newValuesOther.add(newValue);
				constraintsOther.add(otherState.connstructEquivalentConstraint(newValue, otherValue));
				if (!DataStructureUtils.haveNonEmptyIntersection(eqClassThis, boundsOtherTodo)) {
					// case 1 + 2.1
					newValuesThis.add(newValue);
					constraintsThis.add(connstructEquivalentConstraint(newValue, thisValue));
					idxThis++;
				} else {
					// case 2.2
					newValuesThis.add(null);
				}
				idxOther++;
			} else if (thisExclusive.isEmpty()) {
				// case 3
				newBounds.add(eqClassThis);
				newValuesThis.add(newValue);
				constraintsThis.add(connstructEquivalentConstraint(newValue, thisValue));
				if (!DataStructureUtils.haveNonEmptyIntersection(eqClassOther, boundsThisTodo)) {
					// case 3.1
					newValuesOther.add(newValue);
					constraintsOther.add(otherState.connstructEquivalentConstraint(newValue, otherValue));
					idxOther++;
				} else {
					// case 3.2
					newValuesOther.add(null);
				}
				idxThis++;
			} else if (DataStructureUtils.haveNonEmptyIntersection(eqClassThis, eqClassOther)) {
				// case 4
				final Set<Term> intersectionWithNextThis =
						DataStructureUtils.intersection(eqClassThis, boundsOtherTodo);
				final Set<Term> intersectionWithNextOther =
						DataStructureUtils.intersection(eqClassOther, boundsThisTodo);
				newBounds.add(DataStructureUtils.intersection(eqClassThis, eqClassOther));
				if (intersectionWithNextThis.isEmpty() && intersectionWithNextOther.isEmpty()) {
					// case 4.1
					newValuesThis.add(newValue);
					newValuesOther.add(newValue);
					constraintsThis.add(connstructEquivalentConstraint(newValue, thisValue));
					constraintsOther.add(otherState.connstructEquivalentConstraint(newValue, otherValue));
					idxThis++;
					idxOther++;
				} else if (intersectionWithNextThis.isEmpty()) {
					// case 4.2
					newValuesThis.add(newValue);
					newValuesOther.add(null);
					constraintsThis.add(connstructEquivalentConstraint(newValue, thisValue));
					boundsOther.set(idxOther, intersectionWithNextOther);
					idxThis++;
				} else if (intersectionWithNextOther.isEmpty()) {
					// case 4.3
					newValuesThis.add(null);
					newValuesOther.add(newValue);
					constraintsOther.add(otherState.connstructEquivalentConstraint(newValue, otherValue));
					boundsThis.set(idxThis, intersectionWithNextThis);
					idxOther++;
				} else {
					// case 4.4
					newValuesThis.add(null);
					newValuesOther.add(null);
					boundsOther.set(idxOther, intersectionWithNextOther);
					boundsThis.set(idxThis, intersectionWithNextThis);
				}
			} else {
				// case 5
				final IProgramVar oldValueThis = newValuesThis.remove(newValuesThis.size() - 1);
				final IProgramVar oldValueOther = newValuesOther.remove(newValuesOther.size() - 1);
				if (oldValueThis != null) {
					removedValuesThis.add(oldValueThis);
				}
				if (oldValueOther != null) {
					removedValuesOther.add(oldValueOther);
				}
				constraintsThis.add(connstructEquivalentConstraints(newValue, Arrays.asList(thisValue, oldValueThis),
						Operator.LOGICOR));
				constraintsOther.add(otherState.connstructEquivalentConstraints(newValue,
						Arrays.asList(otherValue, oldValueOther), Operator.LOGICOR));
				newValuesThis.add(newValue);
				newValuesOther.add(newValue);
				idxThis++;
				idxOther++;
			}
		}
		// Insert the remaining bounds and values
		final int thisSize = valuesThis.size();
		final int otherSize = valuesOther.size();
		while (idxThis < thisSize) {
			final IProgramVar newValue = mToolkit.createValueVar(valueType);
			newBounds.add(boundsThis.get(idxThis));
			newValuesThis.add(newValue);
			newValuesOther.add(newValue);
			constraintsThis.add(connstructEquivalentConstraint(newValue, valuesThis.get(idxThis)));
			constraintsOther.add(otherState.connstructEquivalentConstraint(newValue, valuesOther.get(otherSize - 1)));
			idxThis++;

		}
		while (idxOther < otherSize) {
			final IProgramVar newValue = mToolkit.createValueVar(valueType);
			newBounds.add(boundsOther.get(idxOther));
			newValuesThis.add(newValue);
			newValuesOther.add(newValue);
			constraintsThis.add(connstructEquivalentConstraint(newValue, valuesThis.get(thisSize - 1)));
			constraintsOther.add(otherState.connstructEquivalentConstraint(newValue, valuesOther.get(idxOther)));
			idxOther++;
		}
		final List<IProgramVarOrConst> nonNullValuesThis =
				newValuesThis.stream().filter(x -> x != null).collect(Collectors.toList());
		final List<IProgramVarOrConst> nonNullValuesOther =
				newValuesOther.stream().filter(x -> x != null).collect(Collectors.toList());
		nonNullValuesThis.addAll(removedValuesThis);
		nonNullValuesOther.addAll(removedValuesOther);
		final STATE substateThis = mToolkit.handleAssumptionBySubdomain(mSubState.addVariables(nonNullValuesThis),
				SmtUtils.and(script, constraintsThis)).removeVariables(removedValuesThis);
		final STATE substateOther =
				mToolkit.handleAssumptionBySubdomain(otherState.mSubState.addVariables(nonNullValuesOther),
						SmtUtils.and(script, constraintsOther)).removeVariables(removedValuesOther);
		return new UnificationResult<>(updateState(substateThis), otherState.updateState(substateOther), newBounds,
				newValuesThis, newValuesOther);
	}

	private static <T> Set<T> unionSets(final Collection<Set<T>> sets) {
		return sets.stream().reduce(Collections.emptySet(), DataStructureUtils::union);
	}

	private ArrayDomainState<STATE> applyDisjunctiveOperator(final ArrayDomainState<STATE> other,
			final IAbstractStateBinaryOperator<STATE> operator) {
		if (isBottom()) {
			return other;
		}
		if (other.isBottom()) {
			return this;
		}
		final SegmentationMap segmentationMap = new SegmentationMap();
		final Set<IProgramVarOrConst> processedArrays = new HashSet<>();
		final List<Term> constraints = new ArrayList<>();
		final Set<IProgramVarOrConst> newVariables = new HashSet<>();
		final Set<IProgramVarOrConst> removedVarsThis = new HashSet<>();
		final Set<IProgramVarOrConst> removedVarsOther = new HashSet<>();
		final Script script = mToolkit.getScript();
		ArrayDomainState<STATE> thisState = this;
		ArrayDomainState<STATE> otherState = other;
		for (final IProgramVarOrConst array : mSegmentationMap.getArrays()) {
			if (processedArrays.contains(array)) {
				continue;
			}
			final Sort sort = array.getSort();
			final IBoogieType boundType = mToolkit.getType(TypeUtils.getIndexSort(sort));
			final IBoogieType valueType = mToolkit.getType(TypeUtils.getInnermostArrayValueSort(sort));
			processedArrays.add(array);
			final Set<IProgramVarOrConst> equivalenceClass = new HashSet<>(getEqualArrays(array));
			equivalenceClass.retainAll(other.getEqualArrays(array));
			processedArrays.addAll(equivalenceClass);
			final List<IProgramVar> newBounds = new ArrayList<>();
			newBounds.add(mToolkit.getMinBound());
			final List<IProgramVar> newValues = new ArrayList<>();
			final UnificationResult<STATE> unificationResult = thisState.unify(otherState,
					mSegmentationMap.getSegmentation(array), other.mSegmentationMap.getSegmentation(array));
			for (final Set<Term> eqClass : unificationResult.getBounds()) {
				final IProgramVar newBoundVar = mToolkit.createBoundVar(boundType);
				newVariables.add(newBoundVar);
				newBounds.add(newBoundVar);
				constraints
						.add(SmtUtils.binaryEquality(script, newBoundVar.getTermVariable(), eqClass.iterator().next()));
			}
			final List<IProgramVar> valuesThis = unificationResult.getFirstValues();
			final List<IProgramVar> valuesOther = unificationResult.getSecondValues();
			thisState = unificationResult.getFirstState();
			otherState = unificationResult.getSecondState();
			for (int i = 0; i < valuesThis.size(); i++) {
				final IProgramVar thisValue = valuesThis.get(i);
				final IProgramVar otherValue = valuesOther.get(i);
				if (thisValue != null && otherValue != null) {
					if (!thisValue.equals(otherValue)) {
						throw new InvalidParameterException("Unification should have returned the same value here.");
					}
					newValues.add(thisValue);
				} else if (thisValue != null) {
					final IProgramVar newValueVar = mToolkit.createValueVar(valueType);
					constraints.add(project(newValueVar, thisValue, thisState.getSubTerm()));
					newVariables.add(newValueVar);
					removedVarsThis.add(thisValue);
					newValues.add(newValueVar);
				} else if (otherValue != null) {
					final IProgramVar newValueVar = mToolkit.createValueVar(valueType);
					constraints.add(project(newValueVar, otherValue, otherState.getSubTerm()));
					newVariables.add(newValueVar);
					removedVarsOther.add(otherValue);
					newValues.add(newValueVar);
				} else {
					// TODO: Return a bottom state here?
					final IProgramVar newValueVar = mToolkit.createValueVar(valueType);
					newVariables.add(newValueVar);
					newValues.add(newValueVar);
				}
			}
			newBounds.add(mToolkit.getMaxBound());
			segmentationMap.addEquivalenceClass(equivalenceClass, new Segmentation(newBounds, newValues));
		}
		removedVarsThis.addAll(mSegmentationMap.getAuxVars());
		removedVarsOther.addAll(other.mSegmentationMap.getAuxVars());
		final STATE substateThis = thisState.getSubState().removeVariables(removedVarsThis);
		final STATE substateOther = otherState.getSubState().removeVariables(removedVarsOther);
		final STATE commonSubstate = operator.apply(substateThis, substateOther);
		final STATE resultingSubstate = mToolkit.handleAssumptionBySubdomain(commonSubstate.addVariables(newVariables),
				SmtUtils.and(script, constraints));
		return updateState(resultingSubstate, segmentationMap).simplify();
	}

	private Term project(final IProgramVar newVar, final IProgramVar oldVar, final Term baseTerm) {
		final TermVariable newTv = newVar.getTermVariable();
		final Term substituted =
				new Substitution(mToolkit.getManagedScript(), Collections.singletonMap(oldVar.getTermVariable(), newTv))
						.transform(baseTerm);
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(substituted.getFreeVars()));
		freeVars.remove(newTv);
		final Term quantified =
				SmtUtils.quantifier(mToolkit.getScript(), QuantifiedFormula.EXISTS, freeVars, substituted);
		return mToolkit.applyQuantifierElimination(quantified);
	}

	@Override
	public ArrayDomainState<STATE> union(final ArrayDomainState<STATE> other) {
		return applyDisjunctiveOperator(other, (a, b) -> a.union(b));
	}

	public ArrayDomainState<STATE> applyWidening(final ArrayDomainState<STATE> other) {
		return applyDisjunctiveOperator(other, mToolkit.getWideningOperator());
	}

	private Pair<List<Set<Term>>, List<IProgramVar>> transformSegmentation(final UnionFind<Term> unionFind,
			final Segmentation segmentation, final Set<TermVariable> excludedVars, final boolean extend) {
		final List<Term> bounds = new ArrayList<>();
		for (final IProgramVar b : segmentation.getBounds()) {
			bounds.add(b.getTermVariable());
		}
		final Set<Term> boundSet = new HashSet<>(bounds);
		final List<IProgramVar> values = new ArrayList<>(segmentation.getValues());
		if (extend) {
			final Script script = mToolkit.getScript();
			for (final Term rep : unionFind.getAllRepresentatives()) {
				if (DataStructureUtils.haveNonEmptyIntersection(unionFind.getEquivalenceClassMembers(rep), boundSet)) {
					continue;
				}
				if (bounds.size() == 2) {
					bounds.add(1, rep);
					values.add(1, values.get(0));
					continue;
				}
				final Term firstConstraint = SmtUtils.less(script, rep, bounds.get(0));
				if (mSubState.evaluate(script, firstConstraint) == EvalResult.TRUE) {
					bounds.add(1, rep);
					values.add(1, values.get(0));
					continue;
				}
				boolean added = false;
				for (int i = 1; i < bounds.size() - 2; i++) {
					final Term prev = bounds.get(i);
					final Term next = bounds.get(i + 1);
					final Term constraint =
							Util.and(script, SmtUtils.leq(script, prev, rep), SmtUtils.less(script, rep, next));
					if (mSubState.evaluate(script, constraint) == EvalResult.TRUE) {
						bounds.add(i + 1, rep);
						values.add(i + 1, values.get(i));
						added = true;
						break;
					}
				}
				if (!added) {
					final Term lastConstraint = SmtUtils.less(script, bounds.get(bounds.size() - 2), rep);
					if (mSubState.evaluate(script, lastConstraint) == EvalResult.TRUE) {
						bounds.add(bounds.size() - 2, rep);
						values.add(values.get(values.size() - 1));
					}
				}
			}
		}
		final List<Set<Term>> eqClasses = new ArrayList<>();
		final Predicate<Term> notExcluded = t -> !DataStructureUtils
				.haveNonEmptyIntersection(new HashSet<>(Arrays.asList(t.getFreeVars())), excludedVars);
		for (final Term b : bounds) {
			unionFind.findAndConstructEquivalenceClassIfNeeded(b);
			final Set<Term> filteredEqClass =
					unionFind.getEquivalenceClassMembers(b).stream().filter(notExcluded).collect(Collectors.toSet());
			eqClasses.add(filteredEqClass);
		}
		return new Pair<>(eqClasses, values);
	}

	@Override
	public boolean isEmpty() {
		return mSubState.isEmpty();
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
		// TODO: Check for compatible array equalities
		final Set<IProgramVarOrConst> thisRemoved = new HashSet<>();
		final Set<IProgramVarOrConst> otherRemoved = new HashSet<>();
		ArrayDomainState<STATE> thisState = this;
		ArrayDomainState<STATE> otherState = other;
		for (final IProgramVarOrConst array : mSegmentationMap.getArrays()) {
			final UnificationResult<STATE> unificationResult = thisState.unify(otherState,
					mSegmentationMap.getSegmentation(array), other.mSegmentationMap.getSegmentation(array));
			final List<IProgramVar> thisValues = unificationResult.getFirstValues();
			final List<IProgramVar> otherValues = unificationResult.getSecondValues();
			thisState = unificationResult.getFirstState();
			otherState = unificationResult.getSecondState();
			for (int i = 0; i < thisValues.size(); i++) {
				final IProgramVar thisValue = thisValues.get(i);
				final IProgramVar otherValue = otherValues.get(i);
				if (thisValue == null && otherValue != null) {
					otherRemoved.add(otherValue);
				}
				if (otherValue == null && thisValue != null) {
					thisRemoved.add(thisValue);
				}
			}
		}
		thisRemoved.addAll(mSegmentationMap.getAuxVars());
		otherRemoved.addAll(other.mSegmentationMap.getAuxVars());
		final STATE substateThis = thisState.getSubState().removeVariables(thisRemoved);
		final STATE substateOther = otherState.getSubState().removeVariables(otherRemoved);
		return substateThis.isSubsetOf(substateOther);
	}

	@Override
	public ArrayDomainState<STATE> compact() {
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		final STATE newSubState = mSubState.compact();
		final Term term = mSubState.getTerm(mToolkit.getScript());
		for (final IProgramVarOrConst a : mSegmentationMap.getArrays()) {
			if (isArrayTop(a, term)) {
				newSegmentationMap.remove(a);
			}
		}
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(newSubState.getVariables());
		newVariables.addAll(newSegmentationMap.getArrays());
		newVariables.retainAll(mVariables);
		return new ArrayDomainState<>(newSubState, newSegmentationMap, newVariables, mToolkit);
	}

	private boolean isArrayTop(final IProgramVarOrConst array, final Term term) {
		if (mSegmentationMap.getEquivalenceClass(array).size() > 1) {
			return false;
		}
		final Segmentation segmentation = mSegmentationMap.getSegmentation(array);
		if (segmentation.size() > 1) {
			return false;
		}
		final TermVariable value = segmentation.getValue(0).getTermVariable();
		final Term valueConstraints = SmtUtils.filterFormula(term, Collections.singleton(value), mToolkit.getScript());
		return SmtUtils.isTrue(valueConstraints);

	}

	@Override
	public Term getTerm(final Script script) {
		if (isBottom()) {
			return script.term("false");
		}
		final Term term = mSubState.getTerm(script);
		final Set<TermVariable> bounds = getTermVars(mSegmentationMap.getBoundVars());
		final Set<TermVariable> values = getTermVars(mSegmentationMap.getValueVars());
		final Term valueTerm = SmtUtils.filterFormula(term, values, script);
		final Term arrayTerm = mSegmentationMap.getTerm(mToolkit.getManagedScript(), valueTerm);
		final Term conjunction = Util.and(script, term, arrayTerm);
		final Set<TermVariable> auxVars = DataStructureUtils.union(bounds, values);
		return SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, auxVars, conjunction);
	}

	private static Set<TermVariable> getTermVars(final Collection<IProgramVar> programVars) {
		return programVars.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
	}

	@Override
	public String toString() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("Arrays: ").append(mSegmentationMap);
		stringBuilder.append(", Substate: ").append(mSubState);
		return stringBuilder.toString();
	}

	@Override
	public String toLogString() {
		return toString();
	}

	public Pair<STATE, Segmentation> getSegmentation(final Expression array) {
		if (array instanceof IdentifierExpression) {
			final IProgramVarOrConst arrayVar = mToolkit.getBoogieVar((IdentifierExpression) array);
			return new Pair<>(mSubState, mSegmentationMap.getSegmentation(arrayVar));
		}
		if (array instanceof ArrayStoreExpression) {
			final ArrayStoreExpression store = (ArrayStoreExpression) array;
			final Expression[] indices = store.getIndices();
			// TODO: Implement for multidim arrays
			if (indices.length == 1) {
				final Expression index = indices[0];
				final Expression value = store.getValue();
				final Pair<STATE, Segmentation> subResult = getSegmentation(store.getArray());
				STATE newSubState = subResult.getFirst();
				final Segmentation segmentation = subResult.getSecond();
				final ArrayDomainState<STATE> tmpState = updateState(newSubState);
				final Pair<Integer, Integer> minMax = tmpState.getContainedBoundIndices(segmentation, index);
				final int min = minMax.getFirst();
				final int max = minMax.getSecond();
				final IProgramVar newMinBound = mToolkit.createBoundVar(index.getType());
				final IProgramVar newMaxBound = mToolkit.createBoundVar(index.getType());
				final IProgramVar newValue = mToolkit.createValueVar(value.getType());
				final Script script = mToolkit.getScript();
				final Term minConstraint =
						SmtUtils.binaryEquality(script, newMinBound.getTermVariable(), mToolkit.getTerm(index));
				final Term maxConstraint = SmtUtils.binaryEquality(script, newMaxBound.getTermVariable(),
						SmtUtils.sum(script, "+", mToolkit.getTerm(index), script.numeral("1")));
				final Term valueConstraint =
						SmtUtils.binaryEquality(script, newValue.getTermVariable(), mToolkit.getTerm(value));
				final Term constraint = SmtUtils.and(script, minConstraint, maxConstraint, valueConstraint);
				newSubState = mToolkit.handleAssumptionBySubdomain(
						newSubState.addVariables(Arrays.asList(newMinBound, newMaxBound, newValue)), constraint);
				final List<IProgramVar> newBounds = new ArrayList<>();
				final List<IProgramVar> newValues = new ArrayList<>();
				for (int i = 0; i < min; i++) {
					newBounds.add(segmentation.getBound(i));
					newValues.add(segmentation.getValue(i));
				}
				final List<IProgramVar> oldValues = new ArrayList<>();
				for (int i = min; i < max; i++) {
					oldValues.add(segmentation.getValue(i));
				}
				final Term minEq = SmtUtils.binaryEquality(script, newMinBound.getTermVariable(),
						segmentation.getBound(min).getTermVariable());
				if (newSubState.evaluate(script, minEq) != EvalResult.TRUE) {
					final IProgramVar freshMinValue = mToolkit.createValueVar(index.getType());
					final Term valueMinConstraint =
							connstructEquivalentConstraints(freshMinValue, oldValues, Operator.LOGICOR);
					newSubState = mToolkit.handleAssumptionBySubdomain(newSubState.addVariable(freshMinValue),
							valueMinConstraint);
					newBounds.add(segmentation.getBound(min));
					newValues.add(freshMinValue);
				}
				newBounds.add(newMinBound);
				newValues.add(newValue);
				newBounds.add(newMaxBound);
				final Term maxEq = SmtUtils.binaryEquality(script, newMaxBound.getTermVariable(),
						segmentation.getBound(max).getTermVariable());
				if (newSubState.evaluate(script, maxEq) != EvalResult.TRUE) {
					final IProgramVar freshMaxValue = mToolkit.createValueVar(index.getType());
					final Term valueMaxConstraint =
							connstructEquivalentConstraints(freshMaxValue, oldValues, Operator.LOGICOR);
					newSubState = mToolkit.handleAssumptionBySubdomain(newSubState.addVariable(freshMaxValue),
							valueMaxConstraint);
					newValues.add(freshMaxValue);
				}
				for (int i = max; i < segmentation.size(); i++) {
					newBounds.add(segmentation.getBound(i));
					newValues.add(segmentation.getValue(i));
				}
				newBounds.add(mToolkit.getMaxBound());
				final Segmentation newSegmentation = new Segmentation(newBounds, newValues);
				return new Pair<>(newSubState, newSegmentation);
			}
		}
		// Otherwise return a top segmentation
		final Pair<IProgramVar, Segmentation> segmentationPair = mToolkit.createTopSegmentation(array.getType());
		return new Pair<>(mSubState.addVariable(segmentationPair.getFirst()), segmentationPair.getSecond());
	}

	private Set<IProgramVarOrConst> getEqualArrays(final IProgramVarOrConst array) {
		return mSegmentationMap.getEquivalenceClass(array);
	}

	private Term connstructEquivalentConstraints(final IProgramVarOrConst var, final List<IProgramVar> others,
			final Operator op) {
		assert op == Operator.LOGICAND || op == Operator.LOGICOR;
		final Script script = mToolkit.getScript();
		final List<Term> xjuncts = new ArrayList<>();
		for (final IProgramVar v : others) {
			if (v != null) {
				xjuncts.add(connstructEquivalentConstraint(var, v));
			}
		}
		return op == Operator.LOGICOR ? SmtUtils.or(script, xjuncts) : SmtUtils.and(script, xjuncts);
	}

	private Term connstructEquivalentConstraint(final IProgramVarOrConst newVariable, final IProgramVar oldVariable) {
		return connstructEquivalentConstraint(newVariable, oldVariable, getSubTerm());
	}

	private Term connstructEquivalentConstraint(final IProgramVarOrConst newVariable, final IProgramVar oldVariable,
			final Term baseTerm) {
		final Script script = mToolkit.getScript();
		final Term newTerm = NonrelationalTermUtils.getTermVar(newVariable);
		final TermVariable oldTerm = oldVariable.getTermVariable();
		final Term constraint = SmtUtils.filterFormula(baseTerm, Collections.singleton(oldTerm), script);
		return new Substitution(script, Collections.singletonMap(oldTerm, newTerm)).transform(constraint);
	}

	@Override
	public EvalResult evaluate(final Script script, final Term term) {
		// TODO: Implement (low priority, should be never called)
		// Idea: Replace all select-terms by fresh aux-vars that are added to boundState and valueState
		// and evaluate on these states
		return EvalResult.UNKNOWN;
	}

	public ArrayDomainState<STATE> updateState(final STATE newSubState, final SegmentationMap newSegmentationMap) {
		return new ArrayDomainState<>(newSubState, newSegmentationMap, mVariables, mToolkit);
	}

	public ArrayDomainState<STATE> updateState(final STATE newSubState) {
		return updateState(newSubState, getSegmentationMap());
	}

	public STATE getSubState() {
		return mSubState;
	}

	public SegmentationMap getSegmentationMap() {
		return new SegmentationMap(mSegmentationMap);
	}

	public Pair<Integer, Integer> getContainedBoundIndices(final Segmentation segmentation, final Expression index) {
		return getContainedBoundIndices(segmentation, mToolkit.getTerm(index));
	}

	private Pair<Integer, Integer> getContainedBoundIndices(final Segmentation segmentation, final Term indexTerm) {
		int min = segmentation.size() - 1;
		final Script script = mToolkit.getScript();
		for (int i = 1; i < segmentation.size(); i++) {
			final TermVariable bound = segmentation.getBound(i).getTermVariable();
			final Term term = SmtUtils.leq(script, bound, indexTerm);
			if (mSubState.evaluate(script, term) != EvalResult.TRUE) {
				min = i - 1;
				break;
			}
		}
		int max = min + 1;
		for (int i = segmentation.size() - 1; i > min; i--) {
			final TermVariable bound = segmentation.getBound(i).getTermVariable();
			final Term term = SmtUtils.less(script, indexTerm, bound);
			if (mSubState.evaluate(script, term) != EvalResult.TRUE) {
				max = i + 1;
				break;
			}
		}
		return new Pair<>(min, max);
	}

	private Set<IProgramVarOrConst> getUnusedVars(final STATE substate, final SegmentationMap segmentationMap) {
		final Set<IProgramVarOrConst> vars = new HashSet<>(substate.getVariables());
		vars.removeAll(mVariables);
		vars.removeAll(segmentationMap.getAuxVars());
		return vars;
	}

	public Set<IProgramVarOrConst> getUnusedAuxVars() {
		return getUnusedVars(mSubState, mSegmentationMap);
	}

	public ArrayDomainState<STATE> removeUnusedAuxVars() {
		return updateState(mSubState.removeVariables(getUnusedAuxVars()));
	}

	private Segmentation simplifySegmentation(final Segmentation segmentation) {
		final Script script = mToolkit.getScript();
		final Term term = getSubTerm();
		int current = 0;
		int next = 1;
		final List<IProgramVar> newBounds = new ArrayList<>();
		final List<IProgramVar> newValues = new ArrayList<>();
		while (next < segmentation.size()) {
			final TermVariable currentValue = segmentation.getValue(current).getTermVariable();
			final TermVariable nextValue = segmentation.getValue(next).getTermVariable();
			final Term currentTerm = SmtUtils.filterFormula(term, Collections.singleton(currentValue), script);
			final Term nextTerm = SmtUtils.filterFormula(term, Collections.singleton(nextValue), script);
			final Substitution substitution =
					new Substitution(mToolkit.getManagedScript(), Collections.singletonMap(nextValue, currentValue));
			final Term currentSubstitutedTerm = substitution.transform(currentTerm);
			final Term nextSubstitutedTerm = substitution.transform(nextTerm);
			final TermVariable currentBound = segmentation.getBound(current).getTermVariable();
			final TermVariable nextBound = segmentation.getBound(next).getTermVariable();
			final Term boundEquality = SmtUtils.binaryEquality(script, currentBound, nextBound);
			if (SmtUtils.areFormulasEquivalent(currentSubstitutedTerm, nextSubstitutedTerm, script)
					|| mSubState.evaluate(script, boundEquality) == EvalResult.TRUE) {
				next++;
			} else {
				newBounds.add(segmentation.getBound(current));
				newValues.add(segmentation.getValue(current));
				current = next++;
			}
		}
		newBounds.add(segmentation.getBound(current));
		newValues.add(segmentation.getValue(current));
		newBounds.add(mToolkit.getMaxBound());
		return new Segmentation(newBounds, newValues);
	}

	private ArrayDomainState<STATE> simplify() {
		final SegmentationMap newSegmentationMap = new SegmentationMap();
		for (final IProgramVarOrConst rep : mSegmentationMap.getAllRepresentatives()) {
			final Segmentation newSegmentation = simplifySegmentation(mSegmentationMap.getSegmentation(rep));
			final Set<IProgramVarOrConst> eqClass = mSegmentationMap.getEquivalenceClass(rep);
			newSegmentationMap.addEquivalenceClass(eqClass, newSegmentation);
		}
		return updateState(mSubState, newSegmentationMap).removeUnusedAuxVars();
	}

	private Term getSubTerm() {
		if (mCachedTerm == null) {
			mCachedTerm = mSubState.getTerm(mToolkit.getScript());
		}
		return mCachedTerm;
	}

	private EquivalenceFinder getEquivalenceFinder() {
		if (mEquivalenceFinder == null) {
			mEquivalenceFinder = mToolkit.createEquivalenceFinder(getSubTerm());
		}
		return mEquivalenceFinder;
	}
}
