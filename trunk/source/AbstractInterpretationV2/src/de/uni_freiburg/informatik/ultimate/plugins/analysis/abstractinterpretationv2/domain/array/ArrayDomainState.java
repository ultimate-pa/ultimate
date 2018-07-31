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
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
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
			IProgramVarOrConst var = v;
			while (var.getSort().isArraySort()) {
				final IBoogieType valueType = mToolkit.getType(TypeUtils.getValueSort(var.getSort()));
				final Pair<IProgramVar, Segmentation> pair = mToolkit.createTopSegmentation(valueType);
				newSegmentationMap.add(var, pair.getSecond());
				var = pair.getFirst();
			}
			nonArrayVars.add(var);
		}
		final STATE newState = mSubState.addVariables(nonArrayVars);
		return new ArrayDomainState<>(newState, newSegmentationMap, newVariables, mToolkit);
	}

	public ArrayDomainState<STATE> addAuxVars(final Collection<IProgramVarOrConst> auxVars) {
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		final List<IProgramVarOrConst> nonArrayVars = new ArrayList<>();
		for (final IProgramVarOrConst v : auxVars) {
			IProgramVarOrConst var = v;
			while (var.getSort().isArraySort()) {
				final IBoogieType valueType = mToolkit.getType(TypeUtils.getValueSort(var.getSort()));
				final Pair<IProgramVar, Segmentation> pair = mToolkit.createTopSegmentation(valueType);
				newSegmentationMap.add(var, pair.getSecond());
				var = pair.getFirst();
			}
			nonArrayVars.add(var);
		}
		final STATE newState = mSubState.addVariables(nonArrayVars);
		return updateState(newState, newSegmentationMap);
	}

	public ArrayDomainState<STATE> addAuxVar(final IProgramVarOrConst auxVar) {
		return addAuxVars(Collections.singleton(auxVar));
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

	public Pair<Segmentation, ArrayDomainState<STATE>> intersectSegmentations(final Segmentation s1,
			final Segmentation s2) {
		final Script script = mToolkit.getScript();
		final List<IProgramVar> bounds = new ArrayList<>();
		final List<IProgramVar> values = new ArrayList<>();
		final IProgramVar minBound = mToolkit.getMinBound();
		final IProgramVar maxBound = mToolkit.getMaxBound();
		bounds.add(minBound);
		final IBoogieType valueType = mToolkit.getType(s1.getValue(0).getSort());
		final IBoogieType boundType = mToolkit.getType(s1.getBound(1).getSort());
		final IProgramVar v0 = mToolkit.createValueVar(valueType);
		values.add(v0);
		final List<Term> constraints = new ArrayList<>();
		constraints.add(mToolkit.connstructEquivalentConstraint(v0, s1.getValue(0), getSubTerm()));
		constraints.add(mToolkit.connstructEquivalentConstraint(v0, s2.getValue(0), getSubTerm()));
		int idx1 = 1;
		int idx2 = 1;
		// TODO: Do we need new bounds here?
		while (idx1 < s1.size() && idx2 < s2.size()) {
			final IProgramVar b1 = s1.getBound(idx1);
			final IProgramVar b2 = s2.getBound(idx2);
			final IProgramVar v1 = s1.getValue(idx1);
			final IProgramVar v2 = s2.getValue(idx2);
			final IProgramVar v1Old = s1.getValue(idx1 - 1);
			final IProgramVar v2Old = s2.getValue(idx2 - 1);
			final Term t1 = b1.getTermVariable();
			final Term t2 = b2.getTermVariable();
			if (mSubState.evaluate(script, SmtUtils.binaryEquality(script, t1, t2)) == EvalResult.TRUE) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				constraints.add(mToolkit.connstructEquivalentConstraint(b, b1, getSubTerm()));
				constraints.add(mToolkit.connstructEquivalentConstraint(v, v1, getSubTerm()));
				constraints.add(mToolkit.connstructEquivalentConstraint(v, v2, getSubTerm()));
				idx1++;
				idx2++;
			} else if (mSubState.evaluate(script, SmtUtils.leq(script, t1, t2)) == EvalResult.TRUE) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				constraints.add(mToolkit.connstructEquivalentConstraint(b, b1, getSubTerm()));
				constraints.add(mToolkit.connstructEquivalentConstraint(v, v1, getSubTerm()));
				constraints.add(mToolkit.connstructEquivalentConstraint(v, v2Old, getSubTerm()));
				idx1++;
			} else if (mSubState.evaluate(script, SmtUtils.geq(script, t1, t2)) == EvalResult.TRUE) {
				final IProgramVar b = mToolkit.createBoundVar(boundType);
				final IProgramVar v = mToolkit.createValueVar(valueType);
				bounds.add(b);
				values.add(v);
				constraints.add(mToolkit.connstructEquivalentConstraint(b, b2, getSubTerm()));
				constraints.add(mToolkit.connstructEquivalentConstraint(v, v1Old, getSubTerm()));
				constraints.add(mToolkit.connstructEquivalentConstraint(v, v2, getSubTerm()));
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
				final TermVariable lowTv = bLow.getTermVariable();
				final TermVariable highTv = bHigh.getTermVariable();
				constraints.add(SmtUtils.leq(script, lowTv, b1.getTermVariable()));
				constraints.add(SmtUtils.leq(script, lowTv, b2.getTermVariable()));
				if (idx1 > 1) {
					constraints.add(SmtUtils.leq(script, lowTv, s1.getBound(idx1 - 1).getTermVariable()));
				}
				if (idx2 > 1) {
					constraints.add(SmtUtils.leq(script, lowTv, s2.getBound(idx2 - 1).getTermVariable()));
				}
				constraints.add(SmtUtils.leq(script, highTv, b1.getTermVariable()));
				constraints.add(SmtUtils.leq(script, highTv, b2.getTermVariable()));
				if (idx1 + 1 < s1.size()) {
					constraints.add(SmtUtils.leq(script, highTv, s1.getBound(idx1 + 1).getTermVariable()));
				}
				if (idx2 + 1 < s2.size()) {
					constraints.add(SmtUtils.leq(script, highTv, s2.getBound(idx2 + 1).getTermVariable()));
				}
				// Value constraints
				constraints.add(SmtUtils.or(script, connstructEquivalentConstraints(vLow, Arrays.asList(v1, v1Old))));
				constraints.add(SmtUtils.or(script, connstructEquivalentConstraints(vLow, Arrays.asList(v2, v2Old))));
				constraints.add(mToolkit.connstructEquivalentConstraint(vHigh, v1, getSubTerm()));
				constraints.add(mToolkit.connstructEquivalentConstraint(vHigh, v2, getSubTerm()));
				idx1++;
				idx2++;
			}
		}
		// Insert the remaining bounds and values
		while (idx1 < s1.size()) {
			final IProgramVar newValue = mToolkit.createValueVar(valueType);
			final IProgramVar newBound = mToolkit.createBoundVar(boundType);
			bounds.add(newBound);
			values.add(newValue);
			final IProgramVar value1 = s1.getValue(idx1);
			final IProgramVar value2 = s2.getValue(s2.size() - 1);
			constraints.add(mToolkit.connstructEquivalentConstraint(newBound, s1.getBound(idx1), getSubTerm()));
			constraints.addAll(connstructEquivalentConstraints(newValue, Arrays.asList(value1, value2)));
			idx1++;

		}
		while (idx2 < s2.size()) {
			final IProgramVar newValue = mToolkit.createValueVar(valueType);
			final IProgramVar newBound = mToolkit.createBoundVar(boundType);
			bounds.add(newBound);
			values.add(newValue);
			final IProgramVar value1 = s1.getValue(s1.size() - 1);
			final IProgramVar value2 = s2.getValue(idx2);
			constraints.add(mToolkit.connstructEquivalentConstraint(newBound, s2.getBound(idx2), getSubTerm()));
			constraints.addAll(connstructEquivalentConstraints(newValue, Arrays.asList(value1, value2)));
			idx2++;

		}
		bounds.add(maxBound);
		final List<IProgramVarOrConst> newVars = new ArrayList<>();
		newVars.addAll(bounds);
		newVars.remove(minBound);
		newVars.remove(maxBound);
		newVars.addAll(values);
		final STATE newState = mToolkit.handleAssumptionBySubdomain(mSubState.addVariables(newVars),
				SmtUtils.and(script, constraints));
		return new Pair<>(new Segmentation(bounds, values), updateState(newState));
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
		ArrayDomainState<STATE> result = new ArrayDomainState<>(state1.intersect(state2), mVariables, mToolkit);
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
			Pair<Segmentation, ArrayDomainState<STATE>> intersectionResult =
					result.intersectSegmentations(firstSegmentation, iterator.next());
			Segmentation segmentation = intersectionResult.getFirst();
			result = intersectionResult.getSecond();
			while (iterator.hasNext()) {
				intersectionResult = result.intersectSegmentations(segmentation, iterator.next());
				result = intersectionResult.getSecond();
				segmentation = intersectionResult.getFirst();
			}
			result.mSegmentationMap.addEquivalenceClass(equivalenceClass, segmentation);
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

	private UnificationResult<STATE> unify(final ArrayDomainState<STATE> other, final Segmentation segmentation,
			final Segmentation otherSegmentation) {
		final Script script = mToolkit.getScript();
		final Segmentation simplifiedThisSegmentation = simplifySegmentation(segmentation);
		final Segmentation simplifiedOtherSegmentation = other.simplifySegmentation(otherSegmentation);
		final Set<Term> thisBounds = new HashSet<>(getTermVars(simplifiedThisSegmentation.getBounds()));
		final Set<Term> otherBounds = new HashSet<>(getTermVars(simplifiedOtherSegmentation.getBounds()));
		final EquivalenceFinder eqThis = getEquivalenceFinder();
		final EquivalenceFinder eqOther = other.getEquivalenceFinder();
		final UnionFind<Term> eqClassesThis = eqThis.getEquivalences(thisBounds);
		final UnionFind<Term> eqClassesOther = eqOther.getEquivalences(otherBounds);
		final Set<Term> varsAsTerms = mVariables.stream().map(IProgramVarOrConst::getTerm).collect(Collectors.toSet());
		final Predicate<Term> isVariable = t -> varsAsTerms.containsAll(Arrays.asList(t.getFreeVars()));
		final Set<Term> oldBoundsThis = unionSets(getEqClasses(thisBounds, eqClassesThis, x -> true));
		final Set<Term> oldBoundsOther = unionSets(getEqClasses(otherBounds, eqClassesOther, x -> true));
		final Set<Term> filteredBoundsThis = oldBoundsThis.stream().filter(isVariable).collect(Collectors.toSet());
		final Set<Term> filteredBoundsOther = oldBoundsOther.stream().filter(isVariable).collect(Collectors.toSet());
		final Set<Term> newBoundsThis = DataStructureUtils.union(oldBoundsThis, filteredBoundsOther);
		final Set<Term> newBoundsOther = DataStructureUtils.union(oldBoundsOther, filteredBoundsThis);
		final UnionFind<Term> eqClassesThisExtended = eqThis.getEquivalences(newBoundsThis);
		final UnionFind<Term> eqClassesOtherExtended = eqOther.getEquivalences(newBoundsOther);
		final Pair<List<Set<Term>>, List<IProgramVar>> transformedThis =
				transformSegmentation(eqClassesThisExtended, simplifiedThisSegmentation, isVariable);
		final Pair<List<Set<Term>>, List<IProgramVar>> transformedOther =
				other.transformSegmentation(eqClassesOtherExtended, simplifiedOtherSegmentation, isVariable);
		final List<Set<Term>> boundEqsThis = transformedThis.getFirst();
		final List<Set<Term>> boundEqsOther = transformedOther.getFirst();
		final List<IProgramVar> valuesThis = transformedThis.getSecond();
		final List<IProgramVar> valuesOther = transformedOther.getSecond();
		final Set<Term> boundsThisTodo = unionSets(boundEqsThis);
		final Set<Term> boundsOtherTodo = unionSets(boundEqsOther);
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
		constraintsThis.add(mToolkit.connstructEquivalentConstraint(newValue0, thisValue0, getSubTerm()));
		constraintsOther.add(mToolkit.connstructEquivalentConstraint(newValue0, otherValue0, other.getSubTerm()));
		int idxThis = 1;
		int idxOther = 1;
		while (idxThis < valuesThis.size() && idxOther < valuesOther.size()) {
			final IProgramVar thisValue = valuesThis.get(idxThis);
			final IProgramVar otherValue = valuesOther.get(idxOther);
			final Set<Term> eqClassThis = boundEqsThis.get(idxThis);
			final Set<Term> eqClassOther = boundEqsOther.get(idxOther);
			boundsThisTodo.removeAll(eqClassThis);
			boundsOtherTodo.removeAll(eqClassOther);
			final Set<Term> thisExclusive = DataStructureUtils.difference(eqClassThis, eqClassOther);
			final Set<Term> otherExclusive = DataStructureUtils.difference(eqClassOther, eqClassThis);
			final IProgramVar newValue = mToolkit.createValueVar(valueType);
			// TODO: Handle if eqClassThis or eqClassOther is empty
			if (otherExclusive.isEmpty()) {
				// case 2
				newBounds.add(eqClassOther);
				newValuesOther.add(newValue);
				constraintsOther.add(mToolkit.connstructEquivalentConstraint(newValue, otherValue, other.getSubTerm()));
				if (!DataStructureUtils.haveNonEmptyIntersection(eqClassThis, boundsOtherTodo)) {
					// case 1 + 2.1
					newValuesThis.add(newValue);
					constraintsThis.add(mToolkit.connstructEquivalentConstraint(newValue, thisValue, getSubTerm()));
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
				constraintsThis.add(mToolkit.connstructEquivalentConstraint(newValue, thisValue, getSubTerm()));
				if (!DataStructureUtils.haveNonEmptyIntersection(eqClassOther, boundsThisTodo)) {
					// case 3.1
					newValuesOther.add(newValue);
					constraintsOther
							.add(mToolkit.connstructEquivalentConstraint(newValue, otherValue, other.getSubTerm()));
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
					constraintsThis.add(mToolkit.connstructEquivalentConstraint(newValue, thisValue, getSubTerm()));
					constraintsOther
							.add(mToolkit.connstructEquivalentConstraint(newValue, otherValue, other.getSubTerm()));
					idxThis++;
					idxOther++;
				} else if (intersectionWithNextThis.isEmpty()) {
					// case 4.2
					newValuesThis.add(newValue);
					newValuesOther.add(null);
					constraintsThis.add(mToolkit.connstructEquivalentConstraint(newValue, thisValue, getSubTerm()));
					boundEqsOther.set(idxOther, intersectionWithNextOther);
					idxThis++;
				} else if (intersectionWithNextOther.isEmpty()) {
					// case 4.3
					newValuesThis.add(null);
					newValuesOther.add(newValue);
					constraintsOther
							.add(mToolkit.connstructEquivalentConstraint(newValue, otherValue, other.getSubTerm()));
					boundEqsThis.set(idxThis, intersectionWithNextThis);
					idxOther++;
				} else {
					// case 4.4
					newValuesThis.add(null);
					newValuesOther.add(null);
					boundEqsOther.set(idxOther, intersectionWithNextOther);
					boundEqsThis.set(idxThis, intersectionWithNextThis);
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
				constraintsThis.add(SmtUtils.or(script,
						connstructEquivalentConstraints(newValue, Arrays.asList(thisValue, oldValueThis))));
				constraintsOther.add(SmtUtils.or(script,
						other.connstructEquivalentConstraints(newValue, Arrays.asList(otherValue, oldValueOther))));
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
			newBounds.add(boundEqsThis.get(idxThis));
			newValuesThis.add(newValue);
			newValuesOther.add(newValue);
			constraintsThis
					.add(mToolkit.connstructEquivalentConstraint(newValue, valuesThis.get(idxThis), getSubTerm()));
			constraintsOther.add(mToolkit.connstructEquivalentConstraint(newValue, valuesOther.get(otherSize - 1),
					other.getSubTerm()));
			idxThis++;

		}
		while (idxOther < otherSize) {
			final IProgramVar newValue = mToolkit.createValueVar(valueType);
			newBounds.add(boundEqsOther.get(idxOther));
			newValuesThis.add(newValue);
			newValuesOther.add(newValue);
			constraintsThis
					.add(mToolkit.connstructEquivalentConstraint(newValue, valuesThis.get(thisSize - 1), getSubTerm()));
			constraintsOther.add(
					mToolkit.connstructEquivalentConstraint(newValue, valuesOther.get(idxOther), other.getSubTerm()));
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
				mToolkit.handleAssumptionBySubdomain(other.mSubState.addVariables(nonNullValuesOther),
						SmtUtils.and(script, constraintsOther)).removeVariables(removedValuesOther);
		return new UnificationResult<>(updateState(substateThis), other.updateState(substateOther), newBounds,
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
		for (final IProgramVarOrConst array : mVariables) {
			final Sort sort = array.getSort();
			if (!sort.isArraySort() || processedArrays.contains(array)) {
				continue;
			}
			processedArrays.add(array);
			final IBoogieType boundType = mToolkit.getType(TypeUtils.getIndexSort(sort));
			final IBoogieType valueType = mToolkit.getType(TypeUtils.getValueSort(sort));
			final UnificationResult<STATE> unificationResult = thisState.unify(otherState,
					mSegmentationMap.getSegmentation(array), other.mSegmentationMap.getSegmentation(array));
			final Set<IProgramVarOrConst> equivalenceClass = new HashSet<>(getEqualArrays(array));
			equivalenceClass.retainAll(other.getEqualArrays(array));
			processedArrays.addAll(equivalenceClass);
			final List<IProgramVar> newBounds = new ArrayList<>();
			newBounds.add(mToolkit.getMinBound());
			final List<IProgramVar> newValues = new ArrayList<>();
			for (final Set<Term> eqClass : unificationResult.getBounds()) {
				final IProgramVar newBoundVar = mToolkit.createBoundVar(boundType);
				newVariables.add(newBoundVar);
				newBounds.add(newBoundVar);
				if (!eqClass.isEmpty()) {
					constraints.add(
							SmtUtils.binaryEquality(script, newBoundVar.getTermVariable(), eqClass.iterator().next()));
				}
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
		return new QuantifierPusher(mToolkit.getManagedScript(), mToolkit.getServices(), false, PqeTechniques.ALL_LOCAL)
				.transform(quantified);
	}

	@Override
	public ArrayDomainState<STATE> union(final ArrayDomainState<STATE> other) {
		return applyDisjunctiveOperator(other, (a, b) -> a.union(b));
	}

	public ArrayDomainState<STATE> applyWidening(final ArrayDomainState<STATE> other) {
		return applyDisjunctiveOperator(other, mToolkit.getWideningOperator());
	}

	private Pair<List<Set<Term>>, List<IProgramVar>> transformSegmentation(final UnionFind<Term> unionFind,
			final Segmentation segmentation, final Predicate<Term> isIncluded) {
		final List<Term> bounds = new ArrayList<>();
		for (final IProgramVar b : segmentation.getBounds()) {
			bounds.add(b.getTermVariable());
		}
		final Set<Term> boundSet = new HashSet<>(bounds);
		final List<IProgramVar> values = new ArrayList<>(segmentation.getValues());
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
		return new Pair<>(getEqClasses(bounds, unionFind, isIncluded), values);
	}

	private static List<Set<Term>> getEqClasses(final Collection<Term> terms, final UnionFind<Term> unionFind,
			final Predicate<Term> include) {
		final List<Set<Term>> eqClasses = new ArrayList<>();
		for (final Term b : terms) {
			unionFind.findAndConstructEquivalenceClassIfNeeded(b);
			final Set<Term> filteredEqClass =
					unionFind.getEquivalenceClassMembers(b).stream().filter(include).collect(Collectors.toSet());
			eqClasses.add(filteredEqClass);
		}
		return eqClasses;
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
		for (final IProgramVarOrConst var : mVariables) {
			if (!var.getSort().isArraySort()) {
				continue;
			}
			final UnificationResult<STATE> unificationResult = thisState.unify(otherState,
					mSegmentationMap.getSegmentation(var), other.mSegmentationMap.getSegmentation(var));
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
		for (final IProgramVarOrConst a : mSegmentationMap.getArrays()) {
			if (isArrayTop(a, getSubTerm())) {
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
		final Set<TermVariable> values = getTermVars(mSegmentationMap.getValueVars());
		final Term filteredTerm = SmtUtils.filterFormula(getSubTerm(), values, script);
		final Term arrayTerm = mSegmentationMap.getTerm(mToolkit.getManagedScript(), filteredTerm);
		final Set<IProgramVarOrConst> auxVars = new HashSet<>(mSegmentationMap.getArrays());
		auxVars.addAll(mSubState.getVariables());
		auxVars.removeAll(mVariables);
		final Set<TermVariable> auxVarTvs =
				auxVars.stream().map(x -> (TermVariable) x.getTerm()).collect(Collectors.toSet());
		return SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, auxVarTvs,
				SmtUtils.and(script, getSubTerm(), arrayTerm));
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

	public Pair<ArrayDomainState<STATE>, Segmentation> getSegmentation(final Expression array) {
		if (array instanceof IdentifierExpression) {
			final IProgramVarOrConst arrayVar = mToolkit.getBoogieVar((IdentifierExpression) array);
			return new Pair<>(this, mSegmentationMap.getSegmentation(arrayVar));
		}
		if (array instanceof ArrayStoreExpression) {
			final ArrayStoreExpression store = (ArrayStoreExpression) array;
			final Expression[] indices = store.getIndices();
			// TODO: Implement for multidim arrays
			if (indices.length == 1) {
				final Expression index = indices[0];
				final Term indexTerm = mToolkit.getTerm(index);
				final Expression value = store.getValue();
				final Pair<ArrayDomainState<STATE>, Segmentation> subResult = getSegmentation(store.getArray());
				final Segmentation segmentation = subResult.getSecond();
				ArrayDomainState<STATE> tmpState = subResult.getFirst();
				final Pair<Integer, Integer> minMax = tmpState.getContainedBoundIndices(segmentation, indexTerm);
				final int min = minMax.getFirst();
				final int max = minMax.getSecond();
				final Script script = mToolkit.getScript();
				final List<Term> constraints = new ArrayList<>();
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
				newBounds.add(segmentation.getBound(min));
				final IProgramVar freshMinValue = mToolkit.createValueVar(value.getType());
				final boolean arrayValues = freshMinValue.getSort().isArraySort();
				if (arrayValues) {
					tmpState = tmpState.addAuxVar(freshMinValue);
					if (oldValues.size() == 1) {
						tmpState.mSegmentationMap.move(freshMinValue, oldValues.get(0));
					}
				} else {
					constraints.add(
							SmtUtils.or(script, tmpState.connstructEquivalentConstraints(freshMinValue, oldValues)));
				}
				newValues.add(freshMinValue);
				final IProgramVar newMinBound = mToolkit.createBoundVar(index.getType());
				constraints.add(SmtUtils.binaryEquality(script, newMinBound.getTermVariable(), indexTerm));
				newBounds.add(newMinBound);
				final IProgramVar newValue = mToolkit.createValueVar(value.getType());
				if (arrayValues) {
					final Pair<ArrayDomainState<STATE>, Segmentation> newSegmentationPair =
							tmpState.getSegmentation(value);
					tmpState = newSegmentationPair.getFirst();
					tmpState.mSegmentationMap.add(newValue, newSegmentationPair.getSecond());
				} else {
					constraints
							.add(SmtUtils.binaryEquality(script, newValue.getTermVariable(), mToolkit.getTerm(value)));
				}
				newValues.add(newValue);
				final IProgramVar newMaxBound = mToolkit.createBoundVar(index.getType());
				constraints.add(SmtUtils.binaryEquality(script, newMaxBound.getTermVariable(),
						SmtUtils.sum(script, "+", indexTerm, script.numeral("1"))));
				newBounds.add(newMaxBound);
				final IProgramVar freshMaxValue = mToolkit.createValueVar(value.getType());
				if (arrayValues) {
					tmpState = tmpState.addAuxVar(freshMaxValue);
					if (oldValues.size() == 1) {
						tmpState.mSegmentationMap.move(freshMaxValue, oldValues.get(0));
					}
				} else {
					constraints.add(
							SmtUtils.or(script, tmpState.connstructEquivalentConstraints(freshMaxValue, oldValues)));
				}
				newValues.add(freshMaxValue);
				for (int i = max; i < segmentation.size(); i++) {
					newBounds.add(segmentation.getBound(i));
					newValues.add(segmentation.getValue(i));
				}
				newBounds.add(mToolkit.getMaxBound());
				final List<IProgramVarOrConst> newVariables = arrayValues ? Arrays.asList(newMinBound, newMaxBound)
						: Arrays.asList(freshMinValue, newMinBound, newValue, newMaxBound, freshMaxValue);
				final STATE newSubState = mToolkit.handleAssumptionBySubdomain(
						tmpState.getSubState().addVariables(newVariables), SmtUtils.and(script, constraints));
				return new Pair<>(tmpState.updateState(newSubState), new Segmentation(newBounds, newValues));
			}
		}
		// Otherwise return a top segmentation
		// TODO: Implement this for multidimensional arrays!
		final Pair<IProgramVar, Segmentation> segmentationPair = mToolkit.createTopSegmentation(array.getType());
		return new Pair<>(updateState(mSubState.addVariable(segmentationPair.getFirst())),
				segmentationPair.getSecond());
	}

	private Set<IProgramVarOrConst> getEqualArrays(final IProgramVarOrConst array) {
		return mSegmentationMap.getEquivalenceClass(array);
	}

	private List<Term> connstructEquivalentConstraints(final IProgramVarOrConst var, final List<IProgramVar> others) {
		final List<Term> constraints = new ArrayList<>();
		for (final IProgramVar v : others) {
			if (v != null) {
				constraints.add(mToolkit.connstructEquivalentConstraint(var, v, getSubTerm()));
			}
		}
		return constraints;
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

	public ArrayDomainState<STATE> updateState(final SegmentationMap newSegmentationMap) {
		return updateState(mSubState, newSegmentationMap);
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

	public Pair<Integer, Integer> getContainedBoundIndices(final Segmentation segmentation, final Term index) {
		int min = segmentation.size() - 1;
		final Script script = mToolkit.getScript();
		for (int i = 1; i < segmentation.size(); i++) {
			final TermVariable bound = segmentation.getBound(i).getTermVariable();
			final Term term = SmtUtils.leq(script, bound, index);
			if (mSubState.evaluate(script, term) != EvalResult.TRUE) {
				min = i - 1;
				break;
			}
		}
		int max = min + 1;
		for (int i = segmentation.size() - 1; i > min; i--) {
			final TermVariable bound = segmentation.getBound(i).getTermVariable();
			final Term term = SmtUtils.less(script, index, bound);
			if (mSubState.evaluate(script, term) != EvalResult.TRUE) {
				max = i + 1;
				break;
			}
		}
		return new Pair<>(min, max);
	}

	public ArrayDomainState<STATE> removeUnusedAuxVars() {
		// final SegmentationMap newSegmentationMap;
		// if (removeArrays) {
		// newSegmentationMap = getSegmentationMap();
		// final List<IProgramVarOrConst> arrays = new ArrayList<>(mSegmentationMap.getArrays());
		// for (final IProgramVarOrConst array : arrays) {
		// if (mVariables.contains(array) || newSegmentationMap.getAuxVars().contains(array)) {
		// continue;
		// }
		// newSegmentationMap.remove(array);
		// if (TypeUtils.getValueSort(array.getSort()).isArraySort()) {
		// arrays.addAll(newSegmentationMap.getSegmentation(array).getValues());
		// }
		// }
		// } else {
		// newSegmentationMap = mSegmentationMap;
		// }
		final Set<IProgramVarOrConst> vars = new HashSet<>(mSubState.getVariables());
		vars.removeAll(mVariables);
		vars.removeAll(mSegmentationMap.getAuxVars());
		return updateState(mSubState.removeVariables(vars));
	}

	private Segmentation simplifySegmentation(final Segmentation segmentation) {
		final Script script = mToolkit.getScript();
		final List<IProgramVar> newBounds = new ArrayList<>();
		final List<IProgramVar> newValues = new ArrayList<>();
		newBounds.add(segmentation.getBound(0));
		newValues.add(segmentation.getValue(0));
		for (int i = 1; i < segmentation.size(); i++) {
			final TermVariable currentBound = segmentation.getBound(i).getTermVariable();
			final TermVariable nextBound = segmentation.getBound(i + 1).getTermVariable();
			final Term boundEquality = SmtUtils.binaryEquality(script, currentBound, nextBound);
			if (mSubState.evaluate(script, boundEquality) == EvalResult.TRUE) {
				continue;
			}
			final IProgramVar currentValue = segmentation.getValue(i);
			final IProgramVar lastValue = newValues.get(newValues.size() - 1);
			if (areValuesEquivalent(currentValue, lastValue)) {
				continue;
			}
			newValues.add(segmentation.getValue(i));
			newBounds.add(segmentation.getBound(i));
		}
		newBounds.add(mToolkit.getMaxBound());
		return new Segmentation(newBounds, newValues);
	}

	private boolean areValuesEquivalent(final IProgramVar v1, final IProgramVar v2) {
		if (v1.getSort().isArraySort()) {
			return mSegmentationMap.getEquivalenceClass(v1).contains(v2);
		}
		final Script script = mToolkit.getScript();
		final TermVariable v1Tv = v1.getTermVariable();
		final TermVariable v2Tv = v2.getTermVariable();
		final Term v1Term = SmtUtils.filterFormula(getSubTerm(), Collections.singleton(v1Tv), script);
		final Term v2Term = SmtUtils.filterFormula(getSubTerm(), Collections.singleton(v2Tv), script);
		final Substitution substitution =
				new Substitution(mToolkit.getManagedScript(), Collections.singletonMap(v1Tv, v2Tv));
		final Term v1Substituted = substitution.transform(v1Term);
		final Term v2Substituted = substitution.transform(v2Term);
		return SmtUtils.areFormulasEquivalent(v1Substituted, v2Substituted, script);
	}

	public ArrayDomainState<STATE> simplify() {
		final SegmentationMap newSegmentationMap = new SegmentationMap();
		for (final IProgramVarOrConst rep : mSegmentationMap.getAllRepresentatives()) {
			final Segmentation newSegmentation = simplifySegmentation(mSegmentationMap.getSegmentation(rep));
			final Set<IProgramVarOrConst> eqClass = mSegmentationMap.getEquivalenceClass(rep);
			newSegmentationMap.addEquivalenceClass(eqClass, newSegmentation);
		}
		return updateState(mSubState, newSegmentationMap).removeUnusedAuxVars();
	}

	public Term getSubTerm() {
		if (mCachedTerm == null) {
			mCachedTerm = mSubState.getTerm(mToolkit.getScript());
		}
		return mCachedTerm;
	}

	private EquivalenceFinder getEquivalenceFinder() {
		if (mEquivalenceFinder == null) {
			mEquivalenceFinder =
					new EquivalenceFinder(getSubTerm(), mToolkit.getServices(), mToolkit.getManagedScript());
		}
		return mEquivalenceFinder;
	}
}
