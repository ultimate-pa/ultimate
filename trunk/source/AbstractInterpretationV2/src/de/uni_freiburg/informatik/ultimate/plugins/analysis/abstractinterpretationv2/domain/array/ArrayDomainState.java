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
	private ArrayDomainToolkit<STATE> mToolkit;
	private Set<IProgramVarOrConst> mVariables;

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

	public ArrayDomainState<STATE> setSegmentationIntersection(final Segmentation s1, final Segmentation s2,
			final Set<IProgramVarOrConst> arrayEquivalenceClass) {
		STATE newState = mSubState;
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
		newState = mToolkit.handleAssumptionBySubdomain(newState,
				getEqualities(v0, Arrays.asList(s1.getValue(0), s2.getValue(0)), Operator.LOGICAND));
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
			final List<Term> constraints = new ArrayList<>();
			if (!b1.equals(maxBound) && !b2.equals(maxBound)
					&& mSubState.evaluate(script, SmtUtils.binaryEquality(script, t1, t2)) == EvalResult.TRUE) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				newState = newState.addVariable(b).addVariable(v);
				constraints.add(getEquality(b, b1));
				constraints.add(getEqualities(v, Arrays.asList(v1, v2), Operator.LOGICAND));
				idx1++;
				idx2++;
			} else if (b2.equals(maxBound)
					|| mSubState.evaluate(script, SmtUtils.leq(script, t1, t2)) == EvalResult.TRUE) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				newState = newState.addVariable(b).addVariable(v);
				constraints.add(getEquality(b, b1));
				constraints.add(getEqualities(v, Arrays.asList(v1, v2Old), Operator.LOGICAND));
				idx1++;
			} else if (b1.equals(maxBound)
					|| mSubState.evaluate(script, SmtUtils.geq(script, t1, t2)) == EvalResult.TRUE) {
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
				constraints.add(getEqualities(vLow, Arrays.asList(v1, v1Old), Operator.LOGICOR));
				constraints.add(getEqualities(vLow, Arrays.asList(v2, v2Old), Operator.LOGICOR));
				constraints.add(getEqualities(vHigh, Arrays.asList(v1, v2), Operator.LOGICAND));
				idx1++;
				idx2++;
			}
			newState = mToolkit.handleAssumptionBySubdomain(newState, SmtUtils.and(script, constraints));
		}
		bounds.add(maxBound);
		final Segmentation segmentation = new Segmentation(bounds, values);
		final SegmentationMap arraySegmentationMap = getSegmentationMap();
		arraySegmentationMap.addEquivalenceClass(arrayEquivalenceClass, simplifySegmentation(newState, segmentation));
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
		return result.removeUnusedAuxVars();
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

	@Override
	public ArrayDomainState<STATE> union(final ArrayDomainState<STATE> other) {
		if (isBottom()) {
			return other;
		}
		if (other.isBottom()) {
			return this;
		}
		final Script script = mToolkit.getScript();
		final ArrayDomainState<STATE> otherRenamed = other.renameSegmentations(this, false);
		final Set<Term> thisBounds = new HashSet<>(getTermVars(mSegmentationMap.getBoundVars()));
		final Set<Term> otherBounds = new HashSet<>(getTermVars(otherRenamed.mSegmentationMap.getBoundVars()));
		final EquivalenceFinder eqThis = mToolkit.createEquivalenceFinder(mSubState);
		final EquivalenceFinder eqOther = mToolkit.createEquivalenceFinder(otherRenamed.mSubState);
		final UnionFind<Term> eqClassesThis = eqThis.getEquivalences(thisBounds);
		final UnionFind<Term> eqClassesOther = eqOther.getEquivalences(otherBounds);
		STATE subState = unionWithoutBounds(mSubState, otherRenamed.mSubState);
		final SegmentationMap segmentationMap = new SegmentationMap();
		final Set<IProgramVarOrConst> processedArrays = new HashSet<>();
		for (final IProgramVarOrConst array : mSegmentationMap.getArrays()) {
			if (processedArrays.contains(array)) {
				continue;
			}
			final Sort sort = array.getSort();
			final IBoogieType boundType = mToolkit.getType(TypeUtils.getIndexSort(sort));
			final IBoogieType valueType = mToolkit.getType(TypeUtils.getInnermostArrayValueSort(sort));
			processedArrays.add(array);
			final Set<IProgramVarOrConst> equivalenceClass = new HashSet<>();
			equivalenceClass.addAll(getEqualArrays(array));
			equivalenceClass.retainAll(other.getEqualArrays(array));
			processedArrays.addAll(equivalenceClass);
			final Segmentation thisSegmentation = mSegmentationMap.getSegmentation(array);
			final Segmentation otherSegmentation = otherRenamed.mSegmentationMap.getSegmentation(array);
			final Set<TermVariable> oldBoundTermsThis = getTermVars(thisSegmentation.getBounds());
			final Set<TermVariable> oldBoundTermsOther = getTermVars(otherSegmentation.getBounds());
			final Set<TermVariable> excludedVars = new HashSet<>();
			excludedVars.addAll(oldBoundTermsThis);
			excludedVars.addAll(oldBoundTermsOther);
			excludedVars.addAll(getTermVars(thisSegmentation.getValues()));
			excludedVars.addAll(getTermVars(otherSegmentation.getValues()));
			int idxThis = 1;
			int idxOther = 1;
			final List<IProgramVar> newBounds = new ArrayList<>();
			final List<IProgramVar> newValues = new ArrayList<>();
			newBounds.add(mToolkit.getMinBound());
			final IProgramVar thisValue0 = thisSegmentation.getValue(0);
			final IProgramVar otherValue0 = otherSegmentation.getValue(0);
			final IProgramVar newValueVar0 = mToolkit.createValueVar(valueType);
			newValues.add(newValueVar0);
			subState = mToolkit.handleAssumptionBySubdomain(subState.addVariable(newValueVar0),
					getEqualities(newValueVar0, Arrays.asList(thisValue0, otherValue0), Operator.LOGICOR));
			final List<Set<Term>> boundsThis = getBoundEquivalences(eqClassesThis, thisSegmentation, excludedVars);
			final List<Set<Term>> boundsOther = getBoundEquivalences(eqClassesOther, otherSegmentation, excludedVars);
			final Set<Term> allBounds = new HashSet<>();
			for (final Set<Term> s : boundsThis) {
				allBounds.addAll(s);
			}
			for (final Set<Term> s : boundsOther) {
				allBounds.addAll(s);
			}
			final Set<Term> boundsThisTodo =
					boundsThis.stream().reduce(Collections.emptySet(), DataStructureUtils::union);
			final Set<Term> boundsOtherTodo =
					boundsOther.stream().reduce(Collections.emptySet(), DataStructureUtils::union);
			// TODO: Extend segmentations with bounds from other one first
			while (idxThis < thisSegmentation.size() && idxOther < otherSegmentation.size()) {
				final TermVariable thisBound = thisSegmentation.getBound(idxThis).getTermVariable();
				final TermVariable otherBound = otherSegmentation.getBound(idxOther).getTermVariable();
				final IProgramVar thisValue = thisSegmentation.getValue(idxThis);
				final IProgramVar otherValue = otherSegmentation.getValue(idxOther);
				eqClassesThis.findAndConstructEquivalenceClassIfNeeded(thisBound);
				eqClassesOther.findAndConstructEquivalenceClassIfNeeded(otherBound);
				final Set<Term> eqClassThis = boundsThis.get(idxThis);
				final Set<Term> eqClassOther = boundsOther.get(idxOther);
				boundsThisTodo.removeAll(eqClassThis);
				boundsOtherTodo.removeAll(eqClassOther);
				final Set<Term> thisExclusive = DataStructureUtils.difference(eqClassThis, eqClassOther);
				final Set<Term> otherExclusive = DataStructureUtils.difference(eqClassOther, eqClassThis);
				final IProgramVar newBoundVar = mToolkit.createBoundVar(boundType);
				final IProgramVar newValueVar = mToolkit.createValueVar(valueType);
				newBounds.add(newBoundVar);
				newValues.add(newValueVar);
				subState = subState.addVariable(newBoundVar).addVariable(newValueVar);
				// TODO: Initialize in all branches
				Term valueAssumption = script.term("true");
				Term boundAssumption = script.term("true");
				if (otherExclusive.isEmpty()) {
					// case 2
					boundAssumption = SmtUtils.binaryEquality(script, newBoundVar.getTermVariable(),
							eqClassOther.iterator().next());
					if (DataStructureUtils.intersection(eqClassThis, boundsOtherTodo).isEmpty()) {
						// case 1 + 2.1
						valueAssumption =
								getEqualities(newValueVar, Arrays.asList(thisValue, otherValue), Operator.LOGICOR);
						idxThis++;
					} else {
						// case 2.2
						valueAssumption = getEquality(newBoundVar, otherValue);
					}
					idxOther++;
				} else if (thisExclusive.isEmpty()) {
					// case 3
					boundAssumption = SmtUtils.binaryEquality(script, newBoundVar.getTermVariable(),
							eqClassThis.iterator().next());
					if (DataStructureUtils.intersection(eqClassOther, boundsThisTodo).isEmpty()) {
						// case 3.1
						valueAssumption =
								getEqualities(newValueVar, Arrays.asList(thisValue, otherValue), Operator.LOGICOR);
						idxOther++;
					} else {
						// case 3.2
						valueAssumption = getEquality(newBoundVar, thisValue);
					}
					idxThis++;
				} else if (!DataStructureUtils.intersection(eqClassThis, eqClassOther).isEmpty()) {
					// case 4
					final Set<Term> intersectionWithNextThis =
							DataStructureUtils.intersection(eqClassThis, boundsOtherTodo);
					final Set<Term> intersectionWithNextOther =
							DataStructureUtils.intersection(eqClassOther, boundsThisTodo);
					if (intersectionWithNextThis.isEmpty() || intersectionWithNextOther.isEmpty()) {
						boundAssumption = SmtUtils.binaryEquality(script, newBoundVar.getTermVariable(),
								eqClassThis.iterator().next());
						if (intersectionWithNextThis.isEmpty() && intersectionWithNextOther.isEmpty()) {
							// case 4.1
							valueAssumption =
									getEqualities(newValueVar, Arrays.asList(thisValue, otherValue), Operator.LOGICOR);
							idxThis++;
							idxOther++;
						} else if (intersectionWithNextThis.isEmpty()) {
							// case 4.2
							valueAssumption = getEquality(newBoundVar, thisValue);
							idxOther++;
						} else {
							// case 4.3
							valueAssumption = getEquality(newBoundVar, thisValue);
							idxThis++;
						}
						idxThis++;
						idxOther++;
					} else {
						// TODO: case 4.4
					}
				} else {
					// TODO: case 5
				}
				final Term assumption = Util.and(script, valueAssumption, boundAssumption);
				subState = mToolkit.handleAssumptionBySubdomain(subState, assumption);
			}
			// Insert the remaining bounds and values
			while (idxThis < thisSegmentation.size()) {
				final IProgramVar boundVar = thisSegmentation.getBound(idxThis);
				final IProgramVar thisValue = thisSegmentation.getValue(idxThis);
				final IProgramVar otherValue = otherSegmentation.getValue(otherSegmentation.size() - 1);
				final IProgramVar newValueVar = mToolkit.createValueVar(valueType);
				newBounds.add(boundVar);
				newValues.add(newValueVar);
				final Term assumption =
						getEqualities(newValueVar, Arrays.asList(thisValue, otherValue), Operator.LOGICOR);
				subState = mToolkit.handleAssumptionBySubdomain(subState.addVariable(newValueVar), assumption);
				idxThis++;

			}
			while (idxOther < otherSegmentation.size()) {
				final IProgramVar boundVar = otherSegmentation.getBound(idxOther);
				final IProgramVar thisValue = thisSegmentation.getValue(thisSegmentation.size() - 1);
				final IProgramVar otherValue = otherSegmentation.getValue(idxOther);
				final IProgramVar newValueVar = mToolkit.createValueVar(valueType);
				newBounds.add(boundVar);
				newValues.add(newValueVar);
				final Term assumption =
						getEqualities(newValueVar, Arrays.asList(thisValue, otherValue), Operator.LOGICOR);
				subState = mToolkit.handleAssumptionBySubdomain(subState.addVariable(newValueVar), assumption);
				idxOther++;
			}
			newBounds.add(mToolkit.getMaxBound());
			segmentationMap.add(array, simplifySegmentation(subState, new Segmentation(newBounds, newValues)));
		}
		return new ArrayDomainState<>(subState, segmentationMap, mVariables, mToolkit).removeUnusedAuxVars();
	}

	private static List<Set<Term>> getBoundEquivalences(final UnionFind<Term> unionFind,
			final Segmentation segmentation, final Set<TermVariable> excludedVars) {
		final List<Set<Term>> result = new ArrayList<>();
		final Predicate<Term> predicate = t -> DataStructureUtils
				.intersection(new HashSet<>(Arrays.asList(t.getFreeVars())), excludedVars).isEmpty();
		for (final IProgramVar var : segmentation.getBounds()) {
			final TermVariable tv = var.getTermVariable();
			unionFind.findAndConstructEquivalenceClassIfNeeded(tv);
			result.add(unionFind.getEquivalenceClassMembers(tv).stream().filter(predicate).collect(Collectors.toSet()));
		}
		return result;
	}

	// TODO: Exclude state2 bounds
	private STATE unionWithoutBounds(final STATE state1, final STATE state2) {
		final Map<IProgramVarOrConst, IProgramVarOrConst> map1 = new HashMap<>();
		final Map<IProgramVarOrConst, IProgramVarOrConst> map2 = new HashMap<>();
		for (final IProgramVarOrConst var : mVariables) {
			final String varName = var.getGloballyUniqueId();
			final IBoogieType type = mToolkit.getType(var.getSort());
			map1.put(var, mToolkit.createVariable(varName, type));
			map2.put(var, mToolkit.createVariable(varName, type));
		}
		final STATE renamedState1 = state1.renameVariables(map1);
		final STATE renamedState2 = state2.renameVariables(map2);
		final STATE completeState1 = renamedState1.addVariables(renamedState2.getVariables());
		final STATE completeState2 = renamedState2.addVariables(renamedState1.getVariables());
		STATE result = completeState1.intersect(completeState2).addVariables(mVariables);
		for (final IProgramVarOrConst var : mVariables) {
			final Term term = getEqualities(var,
					Arrays.asList((IProgramVar) map1.get(var), (IProgramVar) map2.get(var)), Operator.LOGICOR);
			result = mToolkit.handleAssumptionBySubdomain(result, term);
		}
		return result.removeVariables(map1.values()).removeVariables(map2.values());
	}

	public ArrayDomainState<STATE> applyWidening(final ArrayDomainState<STATE> other) {
		// TODO: Implement proper widenning!
		return union(other);
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
		// TODO: Implement this (using unification)
		return SubsetResult.NONE;
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
					final Term valueMinConstraint = getEqualities(freshMinValue, oldValues, Operator.LOGICOR);
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
					final Term valueMaxConstraint = getEqualities(freshMaxValue, oldValues, Operator.LOGICOR);
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

	private Term getEqualities(final IProgramVarOrConst var, final List<IProgramVar> others, final Operator op) {
		assert op == Operator.LOGICAND || op == Operator.LOGICOR;
		final Script script = mToolkit.getScript();
		final Term term = mSubState.getTerm(script);
		final List<Term> xjuncts = new ArrayList<>();
		final Term varTerm = NonrelationalTermUtils.getTermVar(var);
		for (final IProgramVar v : others) {
			final TermVariable other = v.getTermVariable();
			final Term constraint = SmtUtils.filterFormula(term, Collections.singleton(other), script);
			final Term equivalentConstraint =
					new Substitution(script, Collections.singletonMap(other, varTerm)).transform(constraint);
			xjuncts.add(equivalentConstraint);
		}
		return op == Operator.LOGICOR ? SmtUtils.or(script, xjuncts) : SmtUtils.and(script, xjuncts);
	}

	private Term getEquality(final IProgramVarOrConst var1, final IProgramVarOrConst var2) {
		final Term t1 = NonrelationalTermUtils.getTermVar(var1);
		final Term t2 = NonrelationalTermUtils.getTermVar(var2);
		return SmtUtils.binaryEquality(mToolkit.getScript(), t1, t2);
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

	public Set<IProgramVarOrConst> getUnusedAuxVars() {
		final Set<IProgramVarOrConst> vars = new HashSet<>(mSubState.getVariables());
		vars.removeAll(mVariables);
		vars.removeAll(mSegmentationMap.getAuxVars());
		return vars;
	}

	public ArrayDomainState<STATE> removeUnusedAuxVars() {
		return updateState(mSubState.removeVariables(getUnusedAuxVars()));
	}

	// TODO: Remove empty segments
	private Segmentation simplifySegmentation(final STATE subState, final Segmentation segmentation) {
		final Script script = mToolkit.getScript();
		final Term term = subState.getTerm(script);
		int current = 0;
		int next = 1;
		final List<IProgramVar> newBounds = new ArrayList<>();
		final List<IProgramVar> newValues = new ArrayList<>();
		while (next < segmentation.size()) {
			final TermVariable currentValueVar = segmentation.getValue(current).getTermVariable();
			final TermVariable nextValueVar = segmentation.getValue(next).getTermVariable();
			final Term currentTerm = SmtUtils.filterFormula(term, Collections.singleton(currentValueVar), script);
			final Term nextTerm = SmtUtils.filterFormula(term, Collections.singleton(nextValueVar), script);
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
		newBounds.add(segmentation.getBound(current));
		newValues.add(segmentation.getValue(current));
		newBounds.add(mToolkit.getMaxBound());
		return new Segmentation(newBounds, newValues);
	}
}
