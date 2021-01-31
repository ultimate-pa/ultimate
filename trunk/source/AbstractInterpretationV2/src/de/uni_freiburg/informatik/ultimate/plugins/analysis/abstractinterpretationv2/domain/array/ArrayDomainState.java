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
import java.util.function.BinaryOperator;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator.EvalResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

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
	private final Map<Segmentation, Segmentation> mSimplifiedSegmentations;

	private ArrayDomainState(final STATE subState, final SegmentationMap segmentationMap,
			final Set<IProgramVarOrConst> variables, final ArrayDomainToolkit<STATE> toolkit) {
		mSubState = subState;
		mSegmentationMap = segmentationMap;
		mToolkit = toolkit;
		mVariables = variables;
		mSimplifiedSegmentations = new HashMap<>();
		assert checkSegmentationMap();
	}

	private boolean checkSegmentationMap() {
		if (isBottom() || mSegmentationMap.getAllRepresentatives().isEmpty()) {
			return true;
		}
		for (final IProgramVarOrConst var : mVariables) {
			final Sort sort = var.getSort();
			if (!sort.isArraySort()) {
				continue;
			}
			final Sort valueSort = TypeUtils.getValueSort(sort);
			final Segmentation segmentation = getSegmentation(var);
			assert segmentation != null : var + " not in segmentation map of state" + this;
			for (final IProgramVar v : segmentation.getValues()) {
				final Sort sort2 = v.getSort();
				assert valueSort.equals(sort2) : "The value " + v
						+ " has not the sort corresponding to its array variable " + var;
				if (sort2.isArraySort()) {
					assert getSegmentation(v) != null : v + " not in segmentation map of state" + this;
				} else {
					assert mSubState.containsVariable(v) : v + " not in substate of state" + this;
				}
			}
		}
		return true;
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
				final Pair<IProgramVar, Segmentation> pair = mToolkit.createTopSegmentation(var.getSort());
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
				final Pair<IProgramVar, Segmentation> pair = mToolkit.createTopSegmentation(var.getSort());
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
			final boolean wasThere = newVariables.remove(v);
			if (!wasThere) {
				throw new UnsupportedOperationException("Unknown variable " + v);
			}
			if (v.getSort().isArraySort()) {
				newSegmentationMap.remove(v);
			} else {
				nonArrayVars.add(v);
			}
		}
		final STATE newState = mSubState.removeVariables(nonArrayVars);
		return new ArrayDomainState<>(newState, newSegmentationMap, newVariables, mToolkit).removeUnusedAuxVars();
	}

	private ArrayDomainState<STATE> removeAuxVars(final Collection<IProgramVar> auxVars) {
		final LinkedList<IProgramVar> auxVarQueue = new LinkedList<>(auxVars);
		final List<IProgramVarOrConst> nonArrayVars = new ArrayList<>();
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		while (!auxVarQueue.isEmpty()) {
			final IProgramVar var = auxVarQueue.removeFirst();
			if (var.getSort().isArraySort()) {
				final Segmentation segmentation = getSegmentation(var);
				auxVarQueue.addAll(segmentation.getValues());
				newSegmentationMap.remove(var);
			} else {
				nonArrayVars.add(var);
			}
		}
		return updateState(mSubState.removeVariables(nonArrayVars), newSegmentationMap);
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
		final Set<IProgramVarOrConst> oldArrays =
				mVariables.stream().filter(x -> x.getSort().isArraySort()).collect(Collectors.toSet());
		final Set<IProgramVarOrConst> dominatorArrays =
				dominator.mVariables.stream().filter(x -> x.getSort().isArraySort()).collect(Collectors.toSet());
		final Set<IProgramVarOrConst> overwrittenArrays = DataStructureUtils.intersection(oldArrays, dominatorArrays);
		final Set<IProgramVarOrConst> newVariables = DataStructureUtils.union(mVariables, dominator.mVariables);
		final ArrayDomainState<STATE> result =
				new ArrayDomainState<>(newSubState, getSegmentationMap(), newVariables, mToolkit);
		result.mSegmentationMap.removeAll(overwrittenArrays);
		result.mSegmentationMap.putAll(dominator.mSegmentationMap);
		return result.removeUnusedAuxVars();
	}

	public Pair<Segmentation, ArrayDomainState<STATE>> unionSegmentations(final List<Segmentation> segmentations,
			final Sort sort) {
		Pair<Segmentation, ArrayDomainState<STATE>> result = new Pair<>(segmentations.get(0), this);
		for (int i = 1; i < segmentations.size(); i++) {
			result = result.getSecond().applyOperatorToSegmentations(result.getFirst(), segmentations.get(i), sort,
					STATE::union);
		}
		return result;
	}

	public Pair<Segmentation, ArrayDomainState<STATE>> intersectSegmentations(final Segmentation s1,
			final Segmentation s2, final Sort sort) {
		return applyOperatorToSegmentations(s1, s2, sort, STATE::intersect);
	}

	private Pair<Segmentation, ArrayDomainState<STATE>> applyOperatorToSegmentations(final Segmentation s1,
			final Segmentation s2, final Sort sort, final BinaryOperator<STATE> operator) {
		final UnificationResult unificationResult = unify(this, s1, s2);
		final ArrayDomainState<STATE> firstState = unificationResult.getFirstState();
		final ArrayDomainState<STATE> secondState = unificationResult.getSecondState();
		final EqSegmentationConversionResult result =
				firstState.convertEqClassSegmentation(secondState, unificationResult.getSegmentation(), sort);
		final Map<IProgramVar, Segmentation> newSegmentations = result.getNewSegmentations();
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(result.getNewVariables());
		final Set<IProgramVarOrConst> removeVariables1 = new HashSet<>(result.getRemoveVariablesFirstState());
		final Set<IProgramVarOrConst> removeVariables2 = new HashSet<>(result.getRemoveVariablesSecondState());
		final List<Term> constraints = new ArrayList<>(result.getConstraints());
		for (final Entry<IProgramVar, EqClassSegmentation> entry : unificationResult.getAuxVarSegmentations()
				.entrySet()) {
			final IProgramVar var = entry.getKey();
			final EqSegmentationConversionResult result2 =
					firstState.convertEqClassSegmentation(secondState, entry.getValue(), var.getSort());
			newSegmentations.put(var, result2.getSegmentation());
			newSegmentations.putAll(result2.getNewSegmentations());
			constraints.addAll(result2.getConstraints());
			newVariables.addAll(result2.getNewVariables());
			newVariables.addAll(result2.getRemoveVariablesFirstState());
			newVariables.addAll(result2.getRemoveVariablesSecondState());
		}
		final STATE intersection = operator.apply(firstState.getSubState().removeVariables(removeVariables1),
				secondState.getSubState().removeVariables(removeVariables2));
		final STATE newSubState = mToolkit.handleAssumptionBySubdomain(intersection.addVariables(newVariables),
				SmtUtils.and(mToolkit.getScript(), constraints));
		final SegmentationMap newSegmentationMap = firstState.getSegmentationMap();
		for (final Entry<IProgramVar, Segmentation> entry : newSegmentations.entrySet()) {
			newSegmentationMap.put(entry.getKey(), entry.getValue());
		}
		return new Pair<>(result.getSegmentation(), firstState.updateState(newSubState, newSegmentationMap));
	}

	private EqSegmentationConversionResult convertEqClassSegmentation(final ArrayDomainState<STATE> otherState,
			final EqClassSegmentation eqClassSegmentation, final Sort sort) {
		final Sort boundSort = TypeUtils.getIndexSort(sort);
		final Sort valueSort = TypeUtils.getValueSort(sort);
		final List<IProgramVar> newBounds = new ArrayList<>();
		newBounds.add(mToolkit.getMinBound());
		final List<IProgramVar> newValues = new ArrayList<>();
		final List<IProgramVarOrConst> newVariables = new ArrayList<>();
		final List<Term> constraints = new ArrayList<>();
		final Script script = mToolkit.getScript();
		final Set<IProgramVarOrConst> removedVarsThis = new HashSet<>();
		final Set<IProgramVarOrConst> removedVarsOther = new HashSet<>();
		final Map<IProgramVar, Segmentation> newSegmentations = new HashMap<>();
		for (final Set<Term> eqClass : eqClassSegmentation.getBounds()) {
			final IProgramVar newBoundVar = mToolkit.createBoundVar(boundSort);
			newVariables.add(newBoundVar);
			newBounds.add(newBoundVar);
			if (!eqClass.isEmpty()) {
				constraints
						.add(SmtUtils.binaryEquality(script, newBoundVar.getTermVariable(), eqClass.iterator().next()));
			}
		}
		final List<IProgramVar> valuesThis = eqClassSegmentation.getFirstValues();
		final List<IProgramVar> valuesOther = eqClassSegmentation.getSecondValues();
		for (int i = 0; i < valuesThis.size(); i++) {
			final IProgramVar thisValue = valuesThis.get(i);
			final IProgramVar otherValue = valuesOther.get(i);
			if (thisValue != null && otherValue != null) {
				if (!thisValue.equals(otherValue)) {
					throw new InvalidParameterException("Unification should have returned the same value here.");
				}
				newValues.add(thisValue);
			} else if (thisValue != null) {
				final IProgramVar newValueVar = mToolkit.createValueVar(valueSort);
				final LinkedList<IProgramVar> newVarsToProject = new LinkedList<>();
				final LinkedList<IProgramVar> oldVarsToProject = new LinkedList<>();
				newVarsToProject.add(newValueVar);
				oldVarsToProject.add(thisValue);
				newValues.add(newValueVar);
				while (!newVarsToProject.isEmpty()) {
					final IProgramVar newVar = newVarsToProject.remove();
					final IProgramVar oldVar = oldVarsToProject.remove();
					if (newVar.getSort().isArraySort()) {
						final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars = new HashMap<>();
						final Segmentation s = getSegmentation(oldVar);
						for (final IProgramVar b : s.getBounds()) {
							final IProgramVar newBound = mToolkit.createBoundVar(b.getSort());
							oldVarsToProject.add(b);
							newVarsToProject.add(newBound);
							old2newVars.put(b, newBound);
						}
						for (final IProgramVar v : s.getValues()) {
							final IProgramVar newValue = mToolkit.createValueVar(v.getSort());
							oldVarsToProject.add(v);
							newVarsToProject.add(newValue);
							old2newVars.put(v, newValue);
						}
						newSegmentations.put(newVar, createFreshSegmentationCopy(s, old2newVars));
					} else {
						constraints.add(project(newVar, oldVar, getSubTerm()));
						newVariables.add(newVar);
						removedVarsThis.add(oldVar);
					}
				}
			} else if (otherValue != null) {
				final IProgramVar newValueVar = mToolkit.createValueVar(valueSort);
				final LinkedList<IProgramVar> newVarsToProject = new LinkedList<>();
				final LinkedList<IProgramVar> oldVarsToProject = new LinkedList<>();
				newVarsToProject.add(newValueVar);
				oldVarsToProject.add(otherValue);
				newValues.add(newValueVar);
				while (!newVarsToProject.isEmpty()) {
					final IProgramVar newVar = newVarsToProject.remove();
					final IProgramVar oldVar = oldVarsToProject.remove();
					if (newVar.getSort().isArraySort()) {
						final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars = new HashMap<>();
						final Segmentation s = otherState.getSegmentation(oldVar);
						for (final IProgramVar b : s.getBounds()) {
							final IProgramVar newBound = mToolkit.createBoundVar(b.getSort());
							oldVarsToProject.add(b);
							newVarsToProject.add(newBound);
							old2newVars.put(b, newBound);
						}
						for (final IProgramVar v : s.getValues()) {
							final IProgramVar newValue = mToolkit.createValueVar(v.getSort());
							oldVarsToProject.add(v);
							newVarsToProject.add(newValue);
							old2newVars.put(v, newValue);
						}
						newSegmentations.put(newVar, createFreshSegmentationCopy(s, old2newVars));
					} else {
						constraints.add(project(newVar, oldVar, otherState.getSubTerm()));
						newVariables.add(newVar);
						removedVarsOther.add(oldVar);
					}
				}
			} else {
				final IProgramVar newValueVar = mToolkit.createValueVar(valueSort);
				newVariables.add(newValueVar);
				newValues.add(newValueVar);
			}
		}
		newBounds.add(mToolkit.getMaxBound());
		return new EqSegmentationConversionResult(new Segmentation(newBounds, newValues), newSegmentations, constraints,
				newVariables, removedVarsThis, removedVarsOther);
	}

	@Override
	public ArrayDomainState<STATE> intersect(final ArrayDomainState<STATE> other) {
		if (isBottom()) {
			return this;
		}
		if (other.isBottom()) {
			return other;
		}
		final ArrayDomainState<STATE> otherState = other.renameSegmentations(this);
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
				segmentations.add(getSegmentation(eq));
				segmentations.add(otherState.getSegmentation(eq));
			}
			final Iterator<Segmentation> iterator = segmentations.iterator();
			final Segmentation firstSegmentation = iterator.next();
			if (!iterator.hasNext()) {
				// If the segmentations are equal, we can directly set it
				result.mSegmentationMap.add(v, firstSegmentation);
				continue;
			}
			final Sort sort = v.getSort();
			Pair<Segmentation, ArrayDomainState<STATE>> intersectionResult =
					result.intersectSegmentations(firstSegmentation, iterator.next(), sort);
			Segmentation segmentation = intersectionResult.getFirst();
			result = intersectionResult.getSecond();
			while (iterator.hasNext()) {
				intersectionResult = result.intersectSegmentations(segmentation, iterator.next(), sort);
				result = intersectionResult.getSecond();
				segmentation = intersectionResult.getFirst();
			}
			result.mSegmentationMap.addEquivalenceClass(equivalenceClass, segmentation);
		}
		return result.simplify();
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
			newSegmentationMap.put(array, createFreshSegmentationCopy(segmentation, old2newVars));
		}
		final STATE newSubState = mSubState.renameVariables(old2newVars);
		return updateState(newSubState, newSegmentationMap);
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
			final Sort sort = oldVar.getSort();
			old2newVars.put(oldVar, isValue ? mToolkit.createValueVar(sort) : mToolkit.createBoundVar(sort));
		}
		return (IProgramVar) old2newVars.get(oldVar);
	}

	private UnificationResult unify(final ArrayDomainState<STATE> other, final Segmentation segmentation,
			final Segmentation otherSegmentation) {
		assert segmentation.getValue(0).getSort()
				.equals(otherSegmentation.getValue(0).getSort()) : "The segmentations have different sorts.";
		final Script script = mToolkit.getScript();
		final Segmentation simplifiedThisSegmentation = simplifySegmentation(segmentation);
		final Segmentation simplifiedOtherSegmentation = other.simplifySegmentation(otherSegmentation);
		final Set<TermVariable> thisBounds = getTermVars(simplifiedThisSegmentation.getBounds());
		final Set<TermVariable> otherBounds = getTermVars(simplifiedOtherSegmentation.getBounds());
		final EquivalenceFinder eqThis = getEquivalenceFinder();
		final EquivalenceFinder eqOther = other.getEquivalenceFinder();
		final UnionFind<Term> eqClassesThis = eqThis.getEquivalences(thisBounds);
		final UnionFind<Term> eqClassesOther = eqOther.getEquivalences(otherBounds);
		final Set<Term> varsAsTerms = mVariables.stream().map(IProgramVarOrConst::getTerm).collect(Collectors.toSet());
		final Predicate<Term> isVariable = t -> varsAsTerms.containsAll(Arrays.asList(t.getFreeVars()));
		final Set<Term> oldBoundsThis = unionSets(getEqClasses(thisBounds, eqClassesThis));
		final Set<Term> oldBoundsOther = unionSets(getEqClasses(otherBounds, eqClassesOther));
		final Set<Term> filteredBoundsThis = oldBoundsThis.stream().filter(isVariable).collect(Collectors.toSet());
		final Set<Term> filteredBoundsOther = oldBoundsOther.stream().filter(isVariable).collect(Collectors.toSet());
		final Set<Term> newBoundsThis = DataStructureUtils.union(oldBoundsThis, filteredBoundsOther);
		final Set<Term> newBoundsOther = DataStructureUtils.union(oldBoundsOther, filteredBoundsThis);
		final UnionFind<Term> eqClassesThisExtended = eqThis.getEquivalences(newBoundsThis);
		final UnionFind<Term> eqClassesOtherExtended = eqOther.getEquivalences(newBoundsOther);
		final Triple<ArrayDomainState<STATE>, List<Set<Term>>, List<IProgramVar>> transformedThis =
				transformSegmentation(eqClassesThisExtended, simplifiedThisSegmentation, isVariable);
		final Triple<ArrayDomainState<STATE>, List<Set<Term>>, List<IProgramVar>> transformedOther =
				other.transformSegmentation(eqClassesOtherExtended, simplifiedOtherSegmentation, isVariable);
		final ArrayDomainState<STATE> thisState = transformedThis.getFirst();
		final ArrayDomainState<STATE> otherState = transformedOther.getFirst();
		final List<Set<Term>> boundEqsThis = transformedThis.getSecond();
		final List<Set<Term>> boundEqsOther = transformedOther.getSecond();
		final List<IProgramVar> valuesThis = transformedThis.getThird();
		final List<IProgramVar> valuesOther = transformedOther.getThird();
		final Set<Term> boundsThisTodo = unionSets(boundEqsThis);
		final Set<Term> boundsOtherTodo = unionSets(boundEqsOther);
		final List<Term> constraintsThis = new ArrayList<>();
		final List<Term> constraintsOther = new ArrayList<>();
		final SegmentationMap newSegmentationMapThis = thisState.getSegmentationMap();
		final SegmentationMap newSegmentationMapOther = otherState.getSegmentationMap();
		// Here unification starts
		final List<Set<Term>> newBounds = new ArrayList<>();
		final List<IProgramVar> newValuesThis = new ArrayList<>();
		final List<IProgramVar> newValuesOther = new ArrayList<>();
		final List<IProgramVar> removedValuesThis = new ArrayList<>();
		final List<IProgramVar> removedValuesOther = new ArrayList<>();
		final IProgramVar thisValue0 = valuesThis.get(0);
		final IProgramVar otherValue0 = valuesOther.get(0);
		final Sort valueSort = thisValue0.getSort();
		final IProgramVar newValue0 = mToolkit.createValueVar(valueSort);
		newValuesThis.add(newValue0);
		newValuesOther.add(newValue0);
		addEquivalence(newValue0, thisValue0, constraintsThis, newSegmentationMapThis);
		addEquivalence(newValue0, otherValue0, constraintsOther, newSegmentationMapOther);
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
			final IProgramVar newValue = mToolkit.createValueVar(valueSort);
			if (otherExclusive.isEmpty()) {
				// case 2
				newBounds.add(eqClassOther);
				newValuesOther.add(newValue);
				other.addEquivalence(newValue, otherValue, constraintsOther, newSegmentationMapOther);
				if (!DataStructureUtils.haveNonEmptyIntersection(eqClassThis, boundsOtherTodo)) {
					// case 1 + 2.1
					newValuesThis.add(newValue);
					addEquivalence(newValue, thisValue, constraintsThis, newSegmentationMapThis);
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
				addEquivalence(newValue, thisValue, constraintsThis, newSegmentationMapThis);
				if (!DataStructureUtils.haveNonEmptyIntersection(eqClassOther, boundsThisTodo)) {
					// case 3.1
					newValuesOther.add(newValue);
					other.addEquivalence(newValue, otherValue, constraintsOther, newSegmentationMapOther);
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
					addEquivalence(newValue, thisValue, constraintsThis, newSegmentationMapThis);
					other.addEquivalence(newValue, otherValue, constraintsOther, newSegmentationMapOther);
					idxThis++;
					idxOther++;
				} else if (intersectionWithNextThis.isEmpty()) {
					// case 4.2
					newValuesThis.add(newValue);
					newValuesOther.add(null);
					addEquivalence(newValue, thisValue, constraintsThis, newSegmentationMapThis);
					boundEqsOther.set(idxOther, intersectionWithNextOther);
					idxThis++;
				} else if (intersectionWithNextOther.isEmpty()) {
					// case 4.3
					newValuesThis.add(null);
					newValuesOther.add(newValue);
					other.addEquivalence(newValue, otherValue, constraintsOther, newSegmentationMapOther);
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
				// TODO: Handle this for multidim arrays precisely? (using unionSegmentations)
				if (newValue.getSort().isArraySort()) {
					final Pair<IProgramVar, Segmentation> segmentationPair =
							mToolkit.createTopSegmentation(newValue.getSort());
					newSegmentationMapThis.add(newValue, segmentationPair.getSecond());
					newSegmentationMapOther.add(newValue, segmentationPair.getSecond());
				} else {
					constraintsThis.add(SmtUtils.or(script,
							connstructEquivalentConstraints(newValue, Arrays.asList(thisValue, oldValueThis))));
					constraintsOther.add(SmtUtils.or(script,
							other.connstructEquivalentConstraints(newValue, Arrays.asList(otherValue, oldValueOther))));
				}
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
			final IProgramVar newValue = mToolkit.createValueVar(valueSort);
			newBounds.add(boundEqsThis.get(idxThis));
			newValuesThis.add(newValue);
			newValuesOther.add(newValue);
			addEquivalence(newValue, valuesThis.get(idxThis), constraintsThis, newSegmentationMapThis);
			other.addEquivalence(newValue, valuesOther.get(otherSize - 1), constraintsOther, newSegmentationMapOther);
			idxThis++;

		}
		while (idxOther < otherSize) {
			final IProgramVar newValue = mToolkit.createValueVar(valueSort);
			newBounds.add(boundEqsOther.get(idxOther));
			newValuesThis.add(newValue);
			newValuesOther.add(newValue);
			addEquivalence(newValue, valuesThis.get(thisSize - 1), constraintsThis, newSegmentationMapThis);
			other.addEquivalence(newValue, valuesOther.get(idxOther), constraintsOther, newSegmentationMapOther);
			idxOther++;
		}
		final List<IProgramVarOrConst> newVariablesThis =
				newValuesThis.stream().filter(x -> x != null).collect(Collectors.toList());
		final List<IProgramVarOrConst> newVariablesOther =
				newValuesOther.stream().filter(x -> x != null).collect(Collectors.toList());
		newVariablesThis.addAll(removedValuesThis);
		newVariablesOther.addAll(removedValuesOther);
		removedValuesThis.addAll(valuesThis);
		removedValuesThis.removeAll(simplifiedThisSegmentation.getValues());
		removedValuesOther.addAll(valuesOther);
		removedValuesOther.removeAll(simplifiedOtherSegmentation.getValues());
		final STATE substateThis = mToolkit.handleAssumptionBySubdomain(
				thisState.mSubState.addVariables(newVariablesThis), SmtUtils.and(script, constraintsThis));
		final STATE substateOther = mToolkit.handleAssumptionBySubdomain(
				otherState.mSubState.addVariables(newVariablesOther), SmtUtils.and(script, constraintsOther));
		ArrayDomainState<STATE> currentStateThis =
				thisState.updateState(substateThis, newSegmentationMapThis).removeAuxVars(removedValuesThis);
		ArrayDomainState<STATE> currentStateOther =
				otherState.updateState(substateOther, newSegmentationMapOther).removeAuxVars(removedValuesOther);
		final Map<IProgramVar, EqClassSegmentation> auxVarSegmentations = new HashMap<>();
		// Unify the aux-vars recursively
		for (int i = 0; i < newValuesThis.size(); i++) {
			final IProgramVar valueThis = newValuesThis.get(i);
			final IProgramVar valueOther = newValuesOther.get(i);
			if (valueThis == null && valueOther == null) {
				continue;
			}
			if (valueThis != null && valueOther != null && valueThis.getSort().isArraySort()) {
				final Segmentation thisAuxSegmentation = currentStateThis.getSegmentation(valueThis);
				final Segmentation otherAuxSegmentation = currentStateOther.getSegmentation(valueOther);
				final UnificationResult subResult =
						currentStateThis.unify(currentStateOther, thisAuxSegmentation, otherAuxSegmentation);
				currentStateThis = subResult.getFirstState();
				currentStateOther = subResult.getSecondState();
				auxVarSegmentations.put(valueThis, subResult.getSegmentation());
				auxVarSegmentations.putAll(subResult.getAuxVarSegmentations());
			}
		}
		return new UnificationResult(currentStateThis, currentStateOther,
				new EqClassSegmentation(newBounds, newValuesThis, newValuesOther), auxVarSegmentations);
	}

	private void addEquivalence(final IProgramVar newVar, final IProgramVar oldVar, final List<Term> constraints,
			final SegmentationMap segmentationMap) {
		if (newVar.getSort().isArraySort()) {
			segmentationMap.move(newVar, oldVar);
		} else {
			constraints.add(mToolkit.connstructEquivalentConstraint(newVar, oldVar, getSubTerm()));
		}
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
		ArrayDomainState<STATE> thisState = this;
		ArrayDomainState<STATE> otherState = other;
		final List<Term> constraints = new ArrayList<>();
		final Set<IProgramVarOrConst> newVariables = new HashSet<>();
		final Set<IProgramVarOrConst> removeVariablesThis = new HashSet<>();
		final Set<IProgramVarOrConst> removeVariablesOther = new HashSet<>();
		for (final IProgramVarOrConst array : mVariables) {
			if (!array.getSort().isArraySort() || processedArrays.contains(array)) {
				continue;
			}
			processedArrays.add(array);
			final Set<IProgramVarOrConst> equivalenceClass = new HashSet<>(getEqualArrays(array));
			equivalenceClass.retainAll(other.getEqualArrays(array));
			processedArrays.addAll(equivalenceClass);
			final UnificationResult unificationResult =
					thisState.unify(otherState, getSegmentation(array), other.getSegmentation(array));
			thisState = unificationResult.getFirstState();
			otherState = unificationResult.getSecondState();
			final EqSegmentationConversionResult result = thisState.convertEqClassSegmentation(otherState,
					unificationResult.getSegmentation(), array.getSort());
			constraints.addAll(result.getConstraints());
			newVariables.addAll(result.getNewVariables());
			removeVariablesThis.addAll(result.getRemoveVariablesFirstState());
			removeVariablesOther.addAll(result.getRemoveVariablesSecondState());
			segmentationMap.addEquivalenceClass(equivalenceClass, result.getSegmentation());
			final Map<IProgramVar, Segmentation> newSegmentations = result.getNewSegmentations();
			for (final Entry<IProgramVar, EqClassSegmentation> entry : unificationResult.getAuxVarSegmentations()
					.entrySet()) {
				final IProgramVar var = entry.getKey();
				final EqSegmentationConversionResult result2 =
						thisState.convertEqClassSegmentation(otherState, entry.getValue(), var.getSort());
				newSegmentations.put(var, result2.getSegmentation());
				newSegmentations.putAll(result2.getNewSegmentations());
				constraints.addAll(result2.getConstraints());
				newVariables.addAll(result2.getNewVariables());
				removeVariablesThis.addAll(result2.getRemoveVariablesFirstState());
				removeVariablesOther.addAll(result2.getRemoveVariablesSecondState());
			}
			for (final Entry<IProgramVar, Segmentation> entry : newSegmentations.entrySet()) {
				segmentationMap.add(entry.getKey(), entry.getValue());
			}
		}
		removeVariablesThis.addAll(mSegmentationMap.getAuxVars());
		removeVariablesOther.addAll(otherState.mSegmentationMap.getAuxVars());
		final STATE substateThis = thisState.getSubState().removeVariables(removeVariablesThis);
		final STATE substateOther = otherState.getSubState().removeVariables(removeVariablesOther);
		final STATE commonSubstate = operator.apply(substateThis, substateOther);
		final STATE resultingSubstate = mToolkit.handleAssumptionBySubdomain(commonSubstate.addVariables(newVariables),
				SmtUtils.and(mToolkit.getScript(), constraints));
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
		return QuantifierPusher.eliminate(mToolkit.getServices(), mToolkit.getManagedScript(), false,
				PqeTechniques.ALL_LOCAL, quantified);
	}

	@Override
	public ArrayDomainState<STATE> union(final ArrayDomainState<STATE> other) {
		return applyDisjunctiveOperator(other, (a, b) -> a.union(b));
	}

	public ArrayDomainState<STATE> applyWidening(final ArrayDomainState<STATE> other) {
		return applyDisjunctiveOperator(other, mToolkit.getWideningOperator());
	}

	private Triple<ArrayDomainState<STATE>, List<Set<Term>>, List<IProgramVar>> transformSegmentation(
			final UnionFind<Term> unionFind, final Segmentation segmentation, final Predicate<Term> include) {
		ArrayDomainState<STATE> currentState = this;
		final List<Set<Term>> boundEqs = new ArrayList<>();
		final List<Term> bounds = new ArrayList<>();
		final List<IProgramVar> values = new ArrayList<>(segmentation.getValues());
		boundEqs.add(Collections.emptySet());
		bounds.add(mToolkit.getMinBound().getTermVariable());
		final Set<IProgramVar> freshValues = new HashSet<>();
		final Set<IProgramVar> removedValues = new HashSet<>();
		// final List<Term> constraints = new ArrayList<>();
		final Script script = mToolkit.getScript();
		for (int i = 1; i < segmentation.size(); i++) {
			final TermVariable var = segmentation.getBound(i).getTermVariable();
			final Set<Term> eqClass = getEqClass(var, unionFind, include);
			if (eqClass.isEmpty()) {
				final IProgramVar currentValue = values.remove(boundEqs.size());
				final IProgramVar lastValue = values.remove(boundEqs.size() - 1);
				removedValues.add(currentValue);
				removedValues.add(lastValue);
				// TODO: Merge lastValue and currentValue
				final IProgramVar newValue = mToolkit.createValueVar(currentValue.getSort());
				values.add(boundEqs.size() - 1, newValue);
				currentState = currentState.addAuxVar(newValue);
				freshValues.add(newValue);
			} else {
				bounds.add(var);
				boundEqs.add(eqClass);
			}
		}
		removedValues.retainAll(freshValues);
		currentState = currentState.removeAuxVars(removedValues);
		boundEqs.add(Collections.emptySet());
		bounds.add(mToolkit.getMaxBound().getTermVariable());
		final Set<Term> boundSet = new HashSet<>(bounds);
		for (final Term rep : unionFind.getAllRepresentatives()) {
			final Set<Term> eqClass = getEqClass(rep, unionFind, include);
			if (eqClass.isEmpty() || DataStructureUtils
					.haveNonEmptyIntersection(unionFind.getEquivalenceClassMembers(rep), boundSet)) {
				continue;
			}
			if (bounds.size() == 2) {
				bounds.add(1, rep);
				boundEqs.add(1, eqClass);
				values.add(1, values.get(0));
				continue;
			}
			boolean added = false;
			final boolean useCache = !containsProgramVar(rep);
			for (int i = 1; i < bounds.size() - 2; i++) {
				final Term prev = bounds.get(i);
				final Term next = bounds.get(i + 1);
				if (mToolkit.evaluate(mSubState, SmtUtils.leq(script, prev, rep), useCache) == EvalResult.TRUE
						&& mToolkit.evaluate(mSubState, SmtUtils.less(script, rep, next),
								useCache) == EvalResult.TRUE) {
					bounds.add(i + 1, rep);
					boundEqs.add(i + 1, eqClass);
					values.add(i + 1, values.get(i));
					added = true;
					break;
				}
			}
			if (!added) {
				if (mToolkit.evaluate(mSubState, SmtUtils.leq(script, bounds.get(bounds.size() - 2), rep),
						useCache) == EvalResult.TRUE) {
					bounds.add(bounds.size() - 1, rep);
					boundEqs.add(boundEqs.size() - 1, eqClass);
					values.add(values.get(values.size() - 1));
				}
			}
		}
		return new Triple<>(currentState, boundEqs, values);
	}

	private boolean containsProgramVar(final Term term) {
		for (final TermVariable var : term.getFreeVars()) {
			final IProgramVarOrConst pv = mToolkit.getBoogieVar((IdentifierExpression) mToolkit.getExpression(var));
			if (mVariables.contains(pv)) {
				return true;
			}
		}
		return false;
	}

	private static Set<Term> getEqClass(final Term term, final UnionFind<Term> unionFind,
			final Predicate<Term> include) {
		unionFind.findAndConstructEquivalenceClassIfNeeded(term);
		return unionFind.getEquivalenceClassMembers(term).stream().filter(include).collect(Collectors.toSet());
	}

	private static List<Set<Term>> getEqClasses(final Collection<? extends Term> terms,
			final UnionFind<Term> unionFind) {
		return terms.stream().map(x -> getEqClass(x, unionFind, y -> true)).collect(Collectors.toList());
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
		final Set<IProgramVarOrConst> thisRemoved = new HashSet<>();
		final Set<IProgramVarOrConst> otherRemoved = new HashSet<>();
		ArrayDomainState<STATE> thisState = removeUnusedAuxVars();
		ArrayDomainState<STATE> otherState = other.removeUnusedAuxVars();
		for (final IProgramVarOrConst var : mVariables) {
			if (!var.getSort().isArraySort()) {
				continue;
			}
			final UnificationResult unificationResult =
					thisState.unify(otherState, getSegmentation(var), other.getSegmentation(var));
			final Map<IProgramVar, EqClassSegmentation> auxVarSegmentaions = unificationResult.getAuxVarSegmentations();
			final List<IProgramVar> thisValues;
			final List<IProgramVar> otherValues;
			if (auxVarSegmentaions.isEmpty()) {
				thisValues = unificationResult.getFirstValues();
				otherValues = unificationResult.getSecondValues();
			} else {
				thisValues = new ArrayList<>();
				otherValues = new ArrayList<>();
				for (final Entry<IProgramVar, EqClassSegmentation> entry : auxVarSegmentaions.entrySet()) {
					final Sort valueSort = TypeUtils.getValueSort(entry.getKey().getSort());
					if (!valueSort.isArraySort()) {
						final EqClassSegmentation segmentation = entry.getValue();
						thisValues.addAll(segmentation.getFirstValues());
						otherValues.addAll(segmentation.getSecondValues());
					}
				}
			}
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
		// Check for compatible array equalities
		SubsetResult result = substateThis.isSubsetOf(substateOther);
		for (final IProgramVarOrConst var : thisState.mSegmentationMap.getArrays()) {
			if (result == SubsetResult.NONE) {
				break;
			}
			if (!mVariables.contains(var)) {
				continue;
			}
			final Set<IProgramVarOrConst> eqClassThis =
					new HashSet<>(thisState.mSegmentationMap.getEquivalenceClass(var));
			final Set<IProgramVarOrConst> eqClassOther =
					new HashSet<>(otherState.mSegmentationMap.getEquivalenceClass(var));
			eqClassThis.retainAll(mVariables);
			eqClassOther.retainAll(mVariables);
			if (eqClassThis.equals(eqClassOther)) {
				result = result.min(SubsetResult.EQUAL);
			} else if (eqClassOther.containsAll(eqClassThis)) {
				result = result.min(SubsetResult.STRICT);
			} else {
				result = SubsetResult.NONE;
			}
		}
		return result;
	}

	@Override
	public ArrayDomainState<STATE> compact() {
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		final STATE newSubState = mSubState.compact();
		for (final IProgramVarOrConst a : mVariables) {
			if (a.getSort().isArraySort() && isArrayTop(a)) {
				newSegmentationMap.remove(a);
			}
		}
		final Set<IProgramVarOrConst> newVariables = new HashSet<>(newSubState.getVariables());
		newVariables.addAll(newSegmentationMap.getArrays());
		newVariables.retainAll(mVariables);
		return new ArrayDomainState<>(newSubState, newSegmentationMap, newVariables, mToolkit).removeUnusedAuxVars();
	}

	private boolean isArrayTop(final IProgramVarOrConst array) {
		if (mSegmentationMap.getEquivalenceClass(array).size() > 1) {
			return false;
		}
		final Segmentation segmentation = getSegmentation(array);
		if (segmentation.size() > 1) {
			return false;
		}
		final IProgramVar value = segmentation.getValue(0);
		if (value.getSort().isArraySort()) {
			return isArrayTop(value);
		}
		final Term valueConstraints = SmtUtils.filterFormula(getSubTerm(),
				Collections.singleton(value.getTermVariable()), mToolkit.getScript());
		return SmtUtils.isTrueLiteral(valueConstraints);

	}

	@Override
	public Term getTerm(final Script script) {
		if (isBottom()) {
			return script.term("false");
		}
		// If there are no arrays, just return the term of the substate
		if (mSegmentationMap.getAllRepresentatives().isEmpty()) {
			return getSubTerm();
		}
		final Set<IProgramVarOrConst> auxVarPvs = new HashSet<>(mSegmentationMap.getArrays());
		auxVarPvs.addAll(mSubState.getVariables());
		auxVarPvs.removeAll(mVariables);
		final Set<TermVariable> auxVars =
				auxVarPvs.stream().map(x -> (TermVariable) x.getTerm()).collect(Collectors.toSet());
		final UnionFind<Term> unionFind = getEquivalenceFinder().getEquivalences(auxVars);
		// Replace the auxVars with equivalent other terms, if possible
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Term var : auxVars) {
			if (unionFind.find(var) == null) {
				continue;
			}
			// If there is a term without aux-vars equivalent to var, substitute var with it
			for (final Term eq : unionFind.getEquivalenceClassMembers(var)) {
				final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(eq.getFreeVars()));
				if (!DataStructureUtils.haveNonEmptyIntersection(freeVars, auxVars)) {
					substitution.put(var, eq);
					break;
				}
			}
		}
		auxVars.removeAll(substitution.keySet());
		final List<Term> conjuncts = new ArrayList<>();
		conjuncts.add(getSubTerm());
		final Set<TermVariable> bounds = new HashSet<>();
		final ManagedScript managedScript = mToolkit.getManagedScript();
		for (final IProgramVarOrConst array : mSegmentationMap.getArrays()) {
			final Segmentation segmentation = getSegmentation(array);
			final Term arrayVar = NonrelationalTermUtils.getTermVar(array);
			// Add the array equivalences to the term
			for (final IProgramVarOrConst eq : mSegmentationMap.getEquivalenceClass(array)) {
				if (!eq.equals(array)) {
					conjuncts.add(SmtUtils.binaryEquality(script, arrayVar, NonrelationalTermUtils.getTermVar(eq)));
				}
			}
			final Sort boundSort = TypeUtils.getIndexSort(array.getSort());
			for (int i = 0; i < segmentation.size(); i++) {
				// Add the bound constraints
				final List<Term> disjuncts = new ArrayList<>();
				final TermVariable idx = managedScript.constructFreshTermVariable("idx", boundSort);
				final TermVariable prev = segmentation.getBound(i).getTermVariable();
				final TermVariable next = segmentation.getBound(i + 1).getTermVariable();
				if (i > 0) {
					disjuncts.add(SmtUtils.greater(script, prev, idx));
				}
				if (i < segmentation.size() - 1) {
					disjuncts.add(SmtUtils.geq(script, idx, next));
				}
				bounds.add(idx);
				final TermVariable value = segmentation.getValue(i).getTermVariable();
				final Term select = script.term("select", arrayVar, idx);
				disjuncts.add(SmtUtils.binaryEquality(script, value, select));
				conjuncts.add(SmtUtils.or(script, disjuncts));
			}
		}
		final Term body = new SubstitutionWithLocalSimplification(managedScript, substitution)
				.transform(SmtUtils.and(script, conjuncts));
		final Term existsTerm = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, auxVars, body);
		return SmtUtils.quantifier(script, QuantifiedFormula.FORALL, bounds, mToolkit.eliminateQuantifier(existsTerm));
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

	public Segmentation getSegmentation(final IProgramVarOrConst var) {
		return mSegmentationMap.getSegmentation(var);
	}

	public Pair<ArrayDomainState<STATE>, Segmentation> getSegmentation(final Expression expr) {
		if (expr instanceof IdentifierExpression) {
			final IProgramVarOrConst var = mToolkit.getBoogieVar((IdentifierExpression) expr);
			return new Pair<>(this, getSegmentation(var));
		}
		if (expr instanceof ArrayStoreExpression) {
			final ArrayStoreExpression store = (ArrayStoreExpression) expr;
			final Expression[] indices = store.getIndices();
			if (indices.length > 1) {
				throw new UnsupportedOperationException("Multidimensional stores are not supported here");
			}
			final Expression index = indices[0];
			final Term indexTerm = mToolkit.getTerm(index);
			final Expression value = store.getValue();
			final Term valueTerm = mToolkit.getTerm(value);
			final Sort indexSort = indexTerm.getSort();
			final Sort valueSort = valueTerm.getSort();
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
			final IProgramVar freshMinValue = mToolkit.createValueVar(valueSort);
			final boolean arrayValues = freshMinValue.getSort().isArraySort();
			if (arrayValues) {
				final List<Segmentation> segmentations = new ArrayList<>();
				for (final IProgramVar v : oldValues) {
					final Pair<Segmentation, ArrayDomainState<STATE>> pair = tmpState.createEquivalentSegmentation(v);
					segmentations.add(pair.getFirst());
					tmpState = pair.getSecond();
				}
				final Pair<Segmentation, ArrayDomainState<STATE>> resultPair =
						tmpState.unionSegmentations(segmentations, oldValues.get(0).getSort());
				tmpState = resultPair.getSecond();
				tmpState.mSegmentationMap.add(freshMinValue, resultPair.getFirst());
			} else {
				constraints
						.add(SmtUtils.or(script, tmpState.connstructEquivalentConstraints(freshMinValue, oldValues)));
			}
			newValues.add(freshMinValue);
			final IProgramVar newMinBound = mToolkit.createBoundVar(indexSort);
			constraints.add(SmtUtils.binaryEquality(script, newMinBound.getTermVariable(), indexTerm));
			newBounds.add(newMinBound);
			final IProgramVar newValue = mToolkit.createValueVar(valueSort);
			if (arrayValues) {
				final Pair<ArrayDomainState<STATE>, Segmentation> newSegmentationPair = tmpState.getSegmentation(value);
				tmpState = newSegmentationPair.getFirst();
				tmpState.mSegmentationMap.add(newValue, newSegmentationPair.getSecond());
			} else {
				constraints.add(SmtUtils.binaryEquality(script, newValue.getTermVariable(), valueTerm));
			}
			newValues.add(newValue);
			final IProgramVar newMaxBound = mToolkit.createBoundVar(indexSort);
			constraints.add(SmtUtils.binaryEquality(script, newMaxBound.getTermVariable(),
					SmtUtils.sum(script, "+", indexTerm, script.numeral("1"))));
			newBounds.add(newMaxBound);
			final IProgramVar freshMaxValue = mToolkit.createValueVar(valueSort);
			if (arrayValues) {
				final List<Segmentation> segmentations = new ArrayList<>();
				for (final IProgramVar v : oldValues) {
					final Pair<Segmentation, ArrayDomainState<STATE>> pair = tmpState.createEquivalentSegmentation(v);
					segmentations.add(pair.getFirst());
					tmpState = pair.getSecond();
				}
				final Pair<Segmentation, ArrayDomainState<STATE>> resultPair =
						tmpState.unionSegmentations(segmentations, oldValues.get(0).getSort());
				tmpState = resultPair.getSecond();
				tmpState.mSegmentationMap.add(freshMaxValue, resultPair.getFirst());
			} else {
				constraints
						.add(SmtUtils.or(script, tmpState.connstructEquivalentConstraints(freshMaxValue, oldValues)));
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
		// Otherwise return a top segmentation
		final Sort arraySort = mToolkit.getTerm(expr).getSort();
		final Pair<IProgramVar, Segmentation> segmentationPair = mToolkit.createTopSegmentation(arraySort);
		return new Pair<>(addAuxVar(segmentationPair.getFirst()), segmentationPair.getSecond());
	}

	private Pair<Segmentation, ArrayDomainState<STATE>> createEquivalentSegmentation(final IProgramVar var) {
		final Segmentation segmentation = mSegmentationMap.getSegmentation(var);
		final List<Term> constraints = new ArrayList<>();
		final List<IProgramVarOrConst> newVariables = new ArrayList<>();
		final List<IProgramVar> newBounds = new ArrayList<>();
		ArrayDomainState<STATE> newState = this;
		final Map<IProgramVar, Segmentation> newSegmentations = new HashMap<>();
		newBounds.add(mToolkit.getMinBound());
		for (int i = 1; i < segmentation.size(); i++) {
			final IProgramVar b = segmentation.getBound(i);
			final IProgramVar newBound = mToolkit.createBoundVar(b.getSort());
			newBounds.add(newBound);
			newVariables.add(newBound);
			constraints.add(mToolkit.connstructEquivalentConstraint(newBound, b, getSubTerm()));
		}
		newBounds.add(mToolkit.getMaxBound());
		final List<IProgramVar> newValues = new ArrayList<>();
		for (final IProgramVar v : segmentation.getValues()) {
			final Sort sort = v.getSort();
			final IProgramVar newValue = mToolkit.createValueVar(sort);
			if (sort.isArraySort()) {
				final Pair<Segmentation, ArrayDomainState<STATE>> pair = newState.createEquivalentSegmentation(v);
				newState = pair.getSecond();
				newSegmentations.put(newValue, pair.getFirst());
			} else {
				newValues.add(newValue);
				newVariables.add(newValue);
				constraints.add(mToolkit.connstructEquivalentConstraint(newValue, v, getSubTerm()));
			}
		}
		final Segmentation newSegmentation = new Segmentation(newBounds, newValues);
		final STATE newSubstate = mToolkit.handleAssumptionBySubdomain(
				newState.getSubState().addVariables(newVariables), SmtUtils.and(mToolkit.getScript(), constraints));
		if (newSegmentations.isEmpty()) {
			return new Pair<>(newSegmentation, newState.updateState(newSubstate));
		}
		final SegmentationMap newSegmentationMap = newState.getSegmentationMap();
		for (final Entry<IProgramVar, Segmentation> entry : newSegmentations.entrySet()) {
			newSegmentationMap.add(entry.getKey(), entry.getValue());
		}
		return new Pair<>(newSegmentation, newState.updateState(newSubstate, newSegmentationMap));
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
		final boolean useCache = !containsProgramVar(index);
		for (int i = 1; i < segmentation.size(); i++) {
			final TermVariable bound = segmentation.getBound(i).getTermVariable();
			if (mToolkit.evaluate(mSubState, SmtUtils.leq(script, bound, index), useCache) != EvalResult.TRUE) {
				min = i - 1;
				break;
			}
		}
		int max = min + 1;
		for (int i = segmentation.size() - 1; i > min; i--) {
			final TermVariable bound = segmentation.getBound(i).getTermVariable();
			if (mToolkit.evaluate(mSubState, SmtUtils.less(script, index, bound), useCache) != EvalResult.TRUE) {
				max = i + 1;
				break;
			}
		}
		return new Pair<>(min, max);
	}

	private ArrayDomainState<STATE> removeUnusedAuxVars() {
		final LinkedList<IProgramVarOrConst> varsToDo = new LinkedList<>(mVariables);
		final Set<IProgramVarOrConst> processedVars = new HashSet<>();
		final Set<IProgramVarOrConst> newVars = new HashSet<>();
		while (!varsToDo.isEmpty()) {
			final IProgramVarOrConst current = varsToDo.removeLast();
			newVars.add(current);
			if (processedVars.contains(current)) {
				continue;
			}
			if (current.getSort().isArraySort()) {
				if (!mSegmentationMap.getArrays().contains(current)) {
					return null;
				}
				processedVars.addAll(mSegmentationMap.getEquivalenceClass(current));
				final Segmentation segmentation = getSegmentation(current);
				varsToDo.addAll(segmentation.getBounds());
				varsToDo.addAll(segmentation.getValues());
			} else {
				processedVars.add(current);
			}
		}
		final Set<IProgramVarOrConst> removeVars = DataStructureUtils.difference(mSubState.getVariables(), newVars);
		final Set<IProgramVarOrConst> removeFromSegmentationMap =
				DataStructureUtils.difference(mSegmentationMap.getArrays(), newVars);
		if (removeVars.isEmpty() && removeFromSegmentationMap.isEmpty()) {
			return this;
		}
		final SegmentationMap newSegmentationMap = getSegmentationMap();
		newSegmentationMap.removeAll(removeFromSegmentationMap);
		return updateState(mSubState.removeVariables(removeVars), newSegmentationMap);
	}

	private Segmentation simplifySegmentation(final Segmentation segmentation) {
		Segmentation result = mSimplifiedSegmentations.get(segmentation);
		if (result == null) {
			final Script script = mToolkit.getScript();
			final List<IProgramVar> newBounds = new ArrayList<>();
			final List<IProgramVar> newValues = new ArrayList<>();
			newBounds.add(segmentation.getBound(0));
			newValues.add(segmentation.getValue(0));
			for (int i = 1; i < segmentation.size(); i++) {
				final TermVariable currentBound = segmentation.getBound(i).getTermVariable();
				final TermVariable nextBound = segmentation.getBound(i + 1).getTermVariable();
				final Term boundEquality = SmtUtils.binaryEquality(script, currentBound, nextBound);
				if (i + 1 < segmentation.size()
						&& mToolkit.evaluate(mSubState, boundEquality, true) == EvalResult.TRUE) {
					continue;
				}
				final IProgramVar currentValue = segmentation.getValue(i);
				final IProgramVar lastValue = newValues.get(newValues.size() - 1);
				if (areVariablesEquivalent(currentValue, lastValue)) {
					continue;
				}
				newValues.add(segmentation.getValue(i));
				newBounds.add(segmentation.getBound(i));
			}
			newBounds.add(mToolkit.getMaxBound());
			result = new Segmentation(newBounds, newValues);
			mSimplifiedSegmentations.put(segmentation, result);
		}
		return result;
	}

	private boolean areVariablesEquivalent(final IProgramVar v1, final IProgramVar v2) {
		if (v1.equals(v2)) {
			return true;
		}
		if (v1.getSort().isArraySort()) {
			final Segmentation s1 = simplifySegmentation(getSegmentation(v1));
			final Segmentation s2 = simplifySegmentation(getSegmentation(v2));
			// Check if the bounds and values are equivalent
			if (s1.size() != s2.size()) {
				return false;
			}
			final List<IProgramVar> bounds1 = s1.getBounds();
			final List<IProgramVar> bounds2 = s2.getBounds();
			final List<IProgramVar> values1 = s1.getValues();
			final List<IProgramVar> values2 = s2.getValues();
			final int max = s1.size() - 1;
			for (int i = 1; i <= max; i++) {
				if (!areVariablesEquivalent(values1.get(i - 1), values2.get(i - 1))) {
					return false;
				}
				if (!areVariablesEquivalent(bounds1.get(i), bounds2.get(i))) {
					return false;
				}
			}
			return areVariablesEquivalent(values1.get(max), values2.get(max));
		}
		final IProgramVar aux1 = mToolkit.createAuxVar(v1.getSort());
		final IProgramVar aux2 = mToolkit.createAuxVar(v1.getSort());
		final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars1 = new HashMap<>();
		old2newVars1.put(v1, aux1);
		old2newVars1.put(v2, aux2);
		final STATE renamedState1 = mSubState.renameVariables(old2newVars1);
		final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars2 = new HashMap<>();
		old2newVars2.put(v1, aux2);
		old2newVars2.put(v2, aux1);
		final STATE renamedState2 = mSubState.renameVariables(old2newVars2);
		return renamedState1.isEqualTo(renamedState2);
	}

	public ArrayDomainState<STATE> simplify() {
		final SegmentationMap newSegmentationMap = new SegmentationMap();
		for (final IProgramVarOrConst rep : mSegmentationMap.getAllRepresentatives()) {
			final Segmentation newSegmentation = simplifySegmentation(getSegmentation(rep));
			final Set<IProgramVarOrConst> eqClass = mSegmentationMap.getEquivalenceClass(rep);
			newSegmentationMap.addEquivalenceClass(eqClass, newSegmentation);
		}
		return updateState(newSegmentationMap).removeUnusedAuxVars();
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

	@Override
	public Set<ArrayDomainState<STATE>> union(final Set<ArrayDomainState<STATE>> states, final int maxSize) {
		final LinkedList<ArrayDomainState<STATE>> stateList = new LinkedList<>(states);
		final Set<ArrayDomainState<STATE>> result = new HashSet<>(states);
		int numberOfMerges = states.size() - maxSize;
		while (numberOfMerges > 0) {
			// Merge the states in reversed order
			final ArrayDomainState<STATE> state1 = stateList.removeLast();
			final ArrayDomainState<STATE> state2 = stateList.removeLast();
			result.remove(state1);
			result.remove(state2);
			final ArrayDomainState<STATE> newState = state1.union(state2);
			if (result.add(newState)) {
				stateList.add(newState);
				--numberOfMerges;
			} else {
				numberOfMerges -= 2;
			}
		}
		assert result.size() <= maxSize : "Did not reduce enough states";
		return result;
	}

	private class UnificationResult {
		private final ArrayDomainState<STATE> mFirstState;
		private final ArrayDomainState<STATE> mSecondState;
		private final EqClassSegmentation mSegmentation;
		private final Map<IProgramVar, EqClassSegmentation> mAuxVarSegmentations;

		public UnificationResult(final ArrayDomainState<STATE> firstState, final ArrayDomainState<STATE> secondState,
				final EqClassSegmentation segmentation,
				final Map<IProgramVar, EqClassSegmentation> auxVarSegmentations) {
			mFirstState = firstState;
			mSecondState = secondState;
			mSegmentation = segmentation;
			mAuxVarSegmentations = auxVarSegmentations;
		}

		public Map<IProgramVar, EqClassSegmentation> getAuxVarSegmentations() {
			return mAuxVarSegmentations;
		}

		public ArrayDomainState<STATE> getFirstState() {
			return mFirstState;
		}

		public ArrayDomainState<STATE> getSecondState() {
			return mSecondState;
		}

		public EqClassSegmentation getSegmentation() {
			return mSegmentation;
		}

		public List<IProgramVar> getFirstValues() {
			return mSegmentation.getFirstValues();
		}

		public List<IProgramVar> getSecondValues() {
			return mSegmentation.getSecondValues();
		}

		@Override
		public String toString() {
			final StringBuilder stringBuilder = new StringBuilder();
			stringBuilder.append("States:\n");
			stringBuilder.append(mFirstState).append('\n');
			stringBuilder.append(mSecondState).append("\n\n");
			stringBuilder.append("Segmentation: ").append(mSegmentation).append('\n');
			stringBuilder.append("AuxVarSegmentations: ").append(mAuxVarSegmentations).append('\n');
			return stringBuilder.toString();
		}
	}

	private class EqClassSegmentation {
		private final List<Set<Term>> mBounds;
		private final List<IProgramVar> mFirstValues;
		private final List<IProgramVar> mSecondValues;

		public EqClassSegmentation(final List<Set<Term>> bounds, final List<IProgramVar> firstValues,
				final List<IProgramVar> secondValues) {
			mBounds = bounds;
			mFirstValues = firstValues;
			mSecondValues = secondValues;
		}

		public List<Set<Term>> getBounds() {
			return mBounds;
		}

		public List<IProgramVar> getFirstValues() {
			return mFirstValues;
		}

		public List<IProgramVar> getSecondValues() {
			return mSecondValues;
		}

		@Override
		public String toString() {
			final StringBuilder stringBuilder = new StringBuilder();
			stringBuilder.append("{-inf} ").append(mFirstValues.get(0)).append(" / ").append(mSecondValues.get(0));
			for (int i = 0; i < mFirstValues.size() - 1; i++) {
				stringBuilder.append(' ').append(mBounds.get(i).toString().replace('[', '{').replace(']', '}'));
				stringBuilder.append(' ').append(mFirstValues.get(i + 1)).append(" / ")
						.append(mSecondValues.get(i + 1));
			}
			return stringBuilder.append(" {inf}").toString();
		}
	}

	private class EqSegmentationConversionResult {
		private final Segmentation mSegmentation;
		private final Map<IProgramVar, Segmentation> mNewSegmentations;
		private final Collection<Term> mConstraints;
		private final Collection<IProgramVarOrConst> mNewVariables;
		private final Collection<IProgramVarOrConst> mRemoveVariablesFirstState;
		private final Collection<IProgramVarOrConst> mRemoveVariablesSecondState;

		public EqSegmentationConversionResult(final Segmentation segmentation,
				final Map<IProgramVar, Segmentation> newSegmentations, final Collection<Term> constraints,
				final Collection<IProgramVarOrConst> newVariables,
				final Collection<IProgramVarOrConst> removeVariablesFirstState,
				final Collection<IProgramVarOrConst> removeVariablesSecondState) {
			mSegmentation = segmentation;
			mNewSegmentations = newSegmentations;
			mConstraints = constraints;
			mNewVariables = newVariables;
			mRemoveVariablesFirstState = removeVariablesFirstState;
			mRemoveVariablesSecondState = removeVariablesSecondState;
		}

		public Segmentation getSegmentation() {
			return mSegmentation;
		}

		public Map<IProgramVar, Segmentation> getNewSegmentations() {
			return mNewSegmentations;
		}

		public Collection<Term> getConstraints() {
			return mConstraints;
		}

		public Collection<IProgramVarOrConst> getNewVariables() {
			return mNewVariables;
		}

		public Collection<IProgramVarOrConst> getRemoveVariablesFirstState() {
			return mRemoveVariablesFirstState;
		}

		public Collection<IProgramVarOrConst> getRemoveVariablesSecondState() {
			return mRemoveVariablesSecondState;
		}
	}
}
