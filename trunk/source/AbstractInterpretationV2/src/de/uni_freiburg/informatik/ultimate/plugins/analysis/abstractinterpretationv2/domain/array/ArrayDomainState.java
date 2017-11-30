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

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
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
		final Statement assume =
				createAssume(getEqualities(v0, Arrays.asList(s1.getValue(0), s2.getValue(0)), Operator.LOGICAND));
		newState = mToolkit.handleStatementBySubdomain(newState, assume);
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
			final AssumeStatement assume2 = createAssume(SmtUtils.and(script, constraints));
			newState = mToolkit.handleStatementBySubdomain(newState, assume2);
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
		final ArrayDomainState<STATE> renamedState = other.renameSegmentations(this, true);
		final Set<IProgramVarOrConst> auxVars1 = new HashSet<>(mSegmentationMap.getAuxVars());
		final Set<IProgramVarOrConst> auxVars2 = new HashSet<>(renamedState.mSegmentationMap.getAuxVars());
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
				segmentations.add(state1.mSegmentationMap.getSegmentation(eq));
				segmentations.add(state2.mSegmentationMap.getSegmentation(eq));
			}
			if (segmentations.size() < 2) {
				// If the segmentations are equal, we do not need to change it
				continue;
			}
			final Iterator<Segmentation> iterator = segmentations.iterator();
			result = result.setSegmentationIntersection(iterator.next(), iterator.next(), equivalenceClass);
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
		final ArrayDomainState<STATE> otherRenamed = other.renameSegmentations(this, false);
		final Term thisTerm = mSubState.getTerm(mToolkit.getScript());
		final Set<Term> thisBounds = new HashSet<>(getTermVars(mSegmentationMap.getBoundVars()));
		final Term otherTerm = otherRenamed.mSubState.getTerm(mToolkit.getScript());
		final Set<Term> otherBounds = new HashSet<>(getTermVars(otherRenamed.mSegmentationMap.getBoundVars()));
		final UnionFind<Term> eqClassesThis = mToolkit.getEquivalences(thisTerm, thisBounds);
		final UnionFind<Term> eqClassesOther = mToolkit.getEquivalences(otherTerm, otherBounds);
		STATE subState = unionWithoutBounds(mSubState, otherRenamed.mSubState);
		final SegmentationMap segmentationMap = new SegmentationMap();
		final Set<IProgramVarOrConst> processedArrays = new HashSet<>();
		final Script script = mToolkit.getScript();
		for (final IProgramVarOrConst array : mSegmentationMap.getArrays()) {
			if (processedArrays.contains(array)) {
				continue;
			}
			processedArrays.add(array);
			final Set<IProgramVarOrConst> equivalenceClass = new HashSet<>();
			equivalenceClass.addAll(getEqualArrays(array));
			equivalenceClass.retainAll(other.getEqualArrays(array));
			processedArrays.addAll(equivalenceClass);
			final Segmentation thisSegmentation = mSegmentationMap.getSegmentation(array);
			final Segmentation otherSegmentation = otherRenamed.mSegmentationMap.getSegmentation(array);
			final Set<Term> oldBoundTermsThis = new HashSet<>(getTermVars(thisSegmentation.getBounds()));
			final Set<Term> oldBoundTermsOther = new HashSet<>(getTermVars(otherSegmentation.getBounds()));
			final Set<Term> newBoundTerms = new HashSet<>();
			newBoundTerms.addAll(getEquivalentTerms(eqClassesThis, oldBoundTermsThis));
			newBoundTerms.addAll(getEquivalentTerms(eqClassesOther, oldBoundTermsOther));
			final List<IProgramVar> newBounds = new ArrayList<>();
			final List<IProgramVar> newValues = new ArrayList<>();
			for (final Term t : newBoundTerms) {
				final IProgramVar newBoundVar = mToolkit.createBoundVar(mToolkit.getType(t.getSort()));
				subState = mToolkit.handleStatementBySubdomain(subState.addVariable(newBoundVar),
						createAssume(SmtUtils.binaryEquality(script, t, newBoundVar.getTermVariable())));
				if (newBounds.isEmpty()) {
					newBounds.add(newBoundVar);
					continue;
				}
				boolean added = false;
				for (int i = 0; i < newBounds.size(); i++) {
					final IProgramVar bound = newBounds.get(i);
					final Term constraint = SmtUtils.leq(script, t, NonrelationalTermUtils.getTermVar(bound));
					if (subState.evaluate(script, constraint) == EvalResult.TRUE) {
						newBounds.add(i, newBoundVar);
						added = true;
						break;
					}
				}
				if (!added) {
					final IProgramVar lastBound = newBounds.get(newBounds.size() - 1);
					final Term constraint = SmtUtils.geq(script, t, NonrelationalTermUtils.getTermVar(lastBound));
					if (subState.evaluate(script, constraint) == EvalResult.TRUE) {
						newBounds.add(newBoundVar);
					}
				}
			}
			for (int i = 0; i < newBounds.size() + 1; i++) {
				final IProgramVar idxAuxVar =
						mToolkit.createBoundVar(mToolkit.getType(thisSegmentation.getBoundSort()));
				final List<Term> idxConstraints = new ArrayList<>();
				if (i > 0) {
					final TermVariable prevIdx = newBounds.get(i - 1).getTermVariable();
					idxConstraints.add(SmtUtils.leq(script, prevIdx, idxAuxVar.getTermVariable()));
				}
				if (i < newBounds.size()) {
					final TermVariable nextIdx = newBounds.get(i).getTermVariable();
					idxConstraints.add(SmtUtils.less(script, idxAuxVar.getTermVariable(), nextIdx));
				}
				final Term idxConstraint = SmtUtils.and(script, idxConstraints);
				final ArrayDomainState<STATE> tmpThisState = updateState(mToolkit
						.handleStatementBySubdomain(mSubState.addVariable(idxAuxVar), createAssume(idxConstraint)));
				final ArrayDomainState<STATE> tmpOtherState =
						otherRenamed.updateState(mToolkit.handleStatementBySubdomain(
								otherRenamed.mSubState.addVariable(idxAuxVar), createAssume(idxConstraint)));
				final IProgramVar newValueVar =
						mToolkit.createValueVar(mToolkit.getType(thisSegmentation.getValueSort()));
				newValues.add(newValueVar);
				final List<Term> disjuncts = new ArrayList<>();
				final Pair<Integer, Integer> thisMinMax =
						tmpThisState.getContainedBoundIndices(thisSegmentation, idxAuxVar.getTermVariable());
				final Pair<Integer, Integer> otherMinMax =
						tmpOtherState.getContainedBoundIndices(otherSegmentation, idxAuxVar.getTermVariable());
				for (int j = thisMinMax.getFirst(); j < thisMinMax.getSecond(); j++) {
					disjuncts.add(getEquality(newValueVar, thisSegmentation.getValue(j)));
				}
				for (int j = otherMinMax.getFirst(); j < otherMinMax.getSecond(); j++) {
					disjuncts.add(getEquality(newValueVar, otherSegmentation.getValue(j)));
				}
				subState = mToolkit.handleStatementBySubdomain(subState.addVariable(newValueVar),
						createAssume(SmtUtils.or(script, disjuncts)));

			}
			final Segmentation newSegmentation = new Segmentation(newBounds, newValues);
			segmentationMap.addEquivalenceClass(equivalenceClass, simplifySegmentation(subState, newSegmentation));
		}
		return new ArrayDomainState<>(subState, segmentationMap, mVariables, mToolkit).removeUnusedAuxVars();
	}

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
			result = mToolkit.handleStatementBySubdomain(result, createAssume(term));
		}
		return result.removeVariables(map1.values()).removeVariables(map2.values());
	}

	private Set<Term> getEquivalentTerms(final UnionFind<Term> unionFind, final Set<Term> terms) {
		final Set<Term> result = new HashSet<>();
		for (final Term eq : terms) {
			unionFind.findAndConstructEquivalenceClassIfNeeded(eq);
			for (final Term t : unionFind.getEquivalenceClassMembers(eq)) {
				final Set<Term> containedExcludeVars = new HashSet<>(terms);
				containedExcludeVars.retainAll(Arrays.asList(t.getFreeVars()));
				if (containedExcludeVars.isEmpty()) {
					result.add(t);
				}
			}
		}
		return result;
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
		final Term term = mToolkit.simplifyTerm(mSubState.getTerm(script));
		final Set<TermVariable> bounds = getTermVars(mSegmentationMap.getBoundVars());
		final Set<TermVariable> values = getTermVars(mSegmentationMap.getValueVars());
		final Term valueTerm = SmtUtils.filterFormula(term, values, script);
		final Term arrayTerm = mSegmentationMap.getTerm(mToolkit.getManagedScript(), valueTerm);
		final Term conjunction = Util.and(script, term, arrayTerm);
		final Set<TermVariable> auxVars = DataStructureUtils.union(bounds, values);
		final Term quantifiedAuxVars = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, auxVars, conjunction);
		return mToolkit.simplifyTerm(quantifiedAuxVars);
	}

	private Set<TermVariable> getTermVars(final Collection<IProgramVar> programVars) {
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
				newSubState = mToolkit.handleStatementBySubdomain(
						newSubState.addVariables(Arrays.asList(newMinBound, newMaxBound, newValue)),
						createAssume(constraint));
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
					newSubState = mToolkit.handleStatementBySubdomain(newSubState.addVariable(freshMinValue),
							createAssume(valueMinConstraint));
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
					newSubState = mToolkit.handleStatementBySubdomain(newSubState.addVariable(freshMaxValue),
							createAssume(valueMaxConstraint));
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

	private AssumeStatement createAssume(final Term term) {
		return new AssumeStatement(null, mToolkit.getExpression(term));
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
		final STATE newSubState = mSubState.removeVariables(getUnusedAuxVars());
		return new ArrayDomainState<>(newSubState, mSegmentationMap, mVariables, mToolkit);
	}

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
