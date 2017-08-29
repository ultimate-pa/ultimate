/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.AbstractNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 * @param <NODE>
 * @param <FUNCTION>
 */
public class EqConstraintFactory<
			ACTION extends IIcfgTransition<IcfgLocation>,
			NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
			FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {

	private final EqConstraint<ACTION, NODE, FUNCTION> mBottomConstraint;

	private final EqConstraint<ACTION, NODE, FUNCTION> mEmptyConstraint;

	private EqStateFactory<ACTION> mEqStateFactory;

	private final AbstractNodeAndFunctionFactory<NODE, FUNCTION, Term> mEqNodeAndFunctionFactory;

	private final IUltimateServiceProvider mServices;

	private final CfgSmtToolkit mCsToolkit;


	private final NestedMap2<Sort, Integer, NODE> mDimensionToWeqVariableNode;

	public EqConstraintFactory(final AbstractNodeAndFunctionFactory<NODE, FUNCTION, Term> eqNodeAndFunctionFactory,
			final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit) {
		mBottomConstraint = new EqBottomConstraint<>(this);
		mBottomConstraint.freeze();

		mEmptyConstraint = new EqConstraint<>(this);
		mEmptyConstraint.freeze();

		mServices = services;
		mCsToolkit = csToolkit;
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;

		mDimensionToWeqVariableNode = new NestedMap2<>();
	}

	public EqConstraint<ACTION, NODE, FUNCTION> getEmptyConstraint() {
		return mEmptyConstraint;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> getBottomConstraint() {
		return mBottomConstraint;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> unfreeze(final EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		assert constraint.isFrozen();
		if (constraint.isBottom()) {
			return constraint;
		}
		return new EqConstraint<>(constraint);
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>
			getDisjunctiveConstraint(final Collection<EqConstraint<ACTION, NODE, FUNCTION>> constraintList) {
		final Collection<EqConstraint<ACTION, NODE, FUNCTION>> bottomsFiltered = constraintList.stream()
				.filter(cons -> !(cons instanceof EqBottomConstraint)).collect(Collectors.toSet());
		return new EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>(bottomsFiltered, this);
	}

	public EqConstraint<ACTION, NODE, FUNCTION> conjoinFlat(
			final EqConstraint<ACTION, NODE, FUNCTION> constraint1,
			final EqConstraint<ACTION, NODE, FUNCTION> constraint2) {
		return constraint1.meet(constraint2);
	}

	/**
	 * conjunction/intersection/join
	 *
	 * @param conjuncts
	 * @return
	 */
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> conjoinDisjunctiveConstraints(
			final List<EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>> conjuncts) {
		final List<Set<EqConstraint<ACTION, NODE, FUNCTION>>> listOfConstraintSets = conjuncts.stream()
				.map(conjunct -> conjunct.getConstraints()).collect(Collectors.toList());

		final Set<List<EqConstraint<ACTION, NODE, FUNCTION>>> crossProduct =
				VPDomainHelpers.computeCrossProduct(listOfConstraintSets, mServices);

		if (crossProduct == null) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				return getTopDisjunctiveConstraint();
			} else {
				throw new AssertionError("cross product should only return null if there is a timeout");
			}
		}

		// for each tuple in the crossproduct: construct the meet, and add it to the resulting constraintList
		final List<EqConstraint<ACTION, NODE, FUNCTION>> constraintList = crossProduct.stream()
			.map(tuple -> tuple.stream()
					.reduce((constraint1, constraint2) -> constraint1.meet(constraint2)).get())
			.collect(Collectors.toList());
		return getDisjunctiveConstraint(constraintList);
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addFunctionDisequalityFlat(final FUNCTION f1, final FUNCTION f2,
				final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
			if (f1 == f2 || f1.equals(f2)) {
				return inputConstraint;
			}
			final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(
					inputConstraint.getConstraints().stream()
						.map(cons -> addFunctionDisequalityFlat(f1, f2, cons))
						.collect(Collectors.toSet()));
			return result;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> addFunctionDisequalityFlat(final FUNCTION func1, final FUNCTION func2,
			final EqConstraint<ACTION, NODE, FUNCTION> originalState) {
		if (originalState.isBottom()) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}

		if (func1 == func2 || func1.equals(func2)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}

		if (originalState.areUnequal(func1, func2)) {
			// the given identifiers are already equal in the originalState
			return originalState;
		}

		if (originalState.areEqual(func1, func2)) {
			return getBottomConstraint();
		}

		final EqConstraint<ACTION, NODE, FUNCTION> funct1Added = addFunctionFlat(func1, originalState);
		final EqConstraint<ACTION, NODE, FUNCTION> funct2Added = addFunctionFlat(func2, funct1Added);

		final EqConstraint<ACTION, NODE, FUNCTION> newConstraint = unfreeze(funct2Added);
		newConstraint.reportFunctionDisequality(func1, func2);
//		newConstraint.saturate();
		newConstraint.freeze();
		return newConstraint;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> addFunctionEqualityFlat(final FUNCTION func1, final FUNCTION func2,
			final EqConstraint<ACTION, NODE, FUNCTION> originalState) {
		if (originalState.isBottom()) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}

		if (func1 == func2 || func1.equals(func2)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}

		if (originalState.areEqual(func1, func2)) {
			// the given identifiers are already equal in the originalState
			return originalState;
		}

		if (originalState.areUnequal(func1, func2)) {
			return getBottomConstraint();
		}

		final EqConstraint<ACTION, NODE, FUNCTION> funct1Added = addFunctionFlat(func1, originalState);
		final EqConstraint<ACTION, NODE, FUNCTION> funct2Added = addFunctionFlat(func2, funct1Added);

		final EqConstraint<ACTION, NODE, FUNCTION> newConstraint = unfreeze(funct2Added);
		newConstraint.reportFunctionEquality(func1, func2);
//		newConstraint.saturate();
		newConstraint.freeze();
		return newConstraint;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> addWeakEquivalence(final FUNCTION array1,
			final FUNCTION array2, final List<NODE> storeIndex,
			final EqConstraint<ACTION, NODE, FUNCTION> inputConstraint) {

		final EqConstraint<ACTION, NODE, FUNCTION> newConstraint = unfreeze(inputConstraint);
		newConstraint.reportWeakEquivalence(array1, array2, storeIndex);
//		newConstraint.saturate();
		newConstraint.freeze();
		return newConstraint;
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjoinDisjunctiveConstraints(
			final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjunct1,
			final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjunct2) {
		final Set<EqConstraint<ACTION, NODE, FUNCTION>> allConjunctiveConstraints = new HashSet<>();
		allConjunctiveConstraints.addAll(disjunct1.getConstraints());
		allConjunctiveConstraints.addAll(disjunct2.getConstraints());
		return getDisjunctiveConstraint(allConjunctiveConstraints);
	}

	/**
	 * disjunction/union/meet
	 *
	 * @param disjuncts
	 * @return
	 */
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjoinDisjunctiveConstraints(
			final List<EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>> disjuncts) {

		final Set<EqConstraint<ACTION, NODE, FUNCTION>> allConjunctiveConstraints = new HashSet<>();
		for (final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjunct : disjuncts) {
			allConjunctiveConstraints.addAll(disjunct.getConstraints());
		}

		return getDisjunctiveConstraint(allConjunctiveConstraints);
	}

	/**
	 * Disjoin two (conjunctive) EqConstraints without creating an EqDisjunctiveConstraint -- this operation may loose
	 * information.
	 *
	 * Essentially, we only keep constraints that are present in both input constraints.
	 *
	 * @param constraint
	 * @param constraint2
	 * @return
	 */
	public EqConstraint<ACTION, NODE, FUNCTION> disjoinFlat(
			final EqConstraint<ACTION, NODE, FUNCTION> constraint1,
			final EqConstraint<ACTION, NODE, FUNCTION> constraint2) {
		final List<EqConstraint<ACTION, NODE, FUNCTION>> disjuncts = new ArrayList<>();
		disjuncts.add(constraint1);
		disjuncts.add(constraint2);
		return getDisjunctiveConstraint(disjuncts).flatten();
	}

	public EqConstraint<ACTION, NODE, FUNCTION> addEqualityFlat(final NODE node1, final NODE node2,
			final EqConstraint<ACTION, NODE, FUNCTION> originalState) {

//		factory.getBenchmark().unpause(VPSFO.addEqualityClock);
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addEquality(" + node1 + ", " + node2 + ", " + "..." + ")");
//		}
		if (originalState.isBottom()) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}

		if (node1 == node2 || node1.equals(node2)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}

		if (originalState.areEqual(node1, node2)) {
			// the given identifiers are already equal in the originalState
			return originalState;
		}

		if (originalState.areUnequal(node1, node2)) {
			return getBottomConstraint();
		}

		final EqConstraint<ACTION, NODE, FUNCTION> unfrozen = unfreeze(originalState);
		unfrozen.reportEquality(node1, node2);
//		unfrozen.saturate();
		unfrozen.freeze();
		return unfrozen;
	}


	public EqConstraint<ACTION, NODE, FUNCTION> addDisequalityFlat(final NODE node1, final NODE node2,
			final EqConstraint<ACTION, NODE, FUNCTION> originalState) {
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addDisEquality(..)");
//		}
		if (originalState.isBottom()) {
			return originalState;
		}

		if (originalState.areUnequal(node1, node2)) {
			return originalState;
		}

		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (originalState.areEqual(node1, node2)) {
			return getBottomConstraint();
		}

		final EqConstraint<ACTION, NODE, FUNCTION> unfrozen = unfreeze(originalState);
		unfrozen.reportDisequality(node1, node2);
//		unfrozen.saturate();
		unfrozen.freeze();
		return unfrozen;
	}


	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addNode(final NODE nodeToAdd,
			final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> constraint) {

		final Set<EqConstraint<ACTION, NODE, FUNCTION>> newConstraints = new HashSet<>();

		for (final EqConstraint<ACTION, NODE, FUNCTION> cons : constraint.getConstraints()) {
			newConstraints.add(addNodeFlat(nodeToAdd, cons));
		}

		return getDisjunctiveConstraint(newConstraints);
	}

	public EqConstraint<ACTION, NODE, FUNCTION> addNodeFlat(final NODE nodeToAdd,
			final EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		if (constraint.getAllNodes().contains(nodeToAdd)) {
			return constraint;
		}

		final EqConstraint<ACTION, NODE, FUNCTION> unf = unfreeze(constraint);
		unf.addNode(nodeToAdd);
		unf.freeze();

		return unf;
	}


	private EqConstraint<ACTION, NODE, FUNCTION> addFunctionFlat(final FUNCTION func,
			final EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		final EqConstraint<ACTION, NODE, FUNCTION> newConstraint = unfreeze(constraint);
		newConstraint.addFunction(func);
		newConstraint.freeze();
		// TODO propagations
		final EqConstraint<ACTION, NODE, FUNCTION> newConstraintWithPropagations = newConstraint;

		return newConstraintWithPropagations;
	}


	/**
	 *
	 * @param varsToProjectAway
	 * @return
	 */
	public EqConstraint<ACTION, NODE, FUNCTION> projectExistentially(final Collection<TermVariable> varsToProjectAway,
			final EqConstraint<ACTION, NODE, FUNCTION> original) {
		assert original.isFrozen();
		final EqConstraint<ACTION, NODE, FUNCTION> unfrozen = unfreeze(original);

		for (final TermVariable var : varsToProjectAway) {
			if (!unfrozen.getAllTermVariables().contains(var)) {
				// nothing to do
				continue;
			}
			if (var.getSort().isArraySort()) {
				// havoccing an array
				final FUNCTION functionToHavoc = getEqNodeAndFunctionFactory().getExistingFunction(var);
				unfrozen.removeFunction(functionToHavoc);
			} else {
				// havoccing an element
				final NODE nodeToHavoc = getEqNodeAndFunctionFactory().getExistingNode(var);
				unfrozen.removeElement(nodeToHavoc);
			}
		}

		unfrozen.freeze();
		assert VPDomainHelpers.constraintFreeOfVars(varsToProjectAway, unfrozen, getMgdScript().getScript()) :
					"resulting constraint still has at least one of the to-be-projected vars";

		return unfrozen;
	}

	public EqStateFactory<ACTION> getEqStateFactory() {
		return mEqStateFactory;
	}

	public void setEqStateFactory(final EqStateFactory<ACTION> eqStateFactory) {
		mEqStateFactory = eqStateFactory;
	}

	public AbstractNodeAndFunctionFactory<NODE, FUNCTION, Term> getEqNodeAndFunctionFactory() {
		return mEqNodeAndFunctionFactory;
	}

	public NODE getWeqVariableNodeForDimension(final int dimensionNumber, final Sort sort) {
		NODE result = mDimensionToWeqVariableNode.get(sort, dimensionNumber);
		if (result == null) {
			final TermVariable tv = getMgdScript().constructFreshTermVariable("weq" + dimensionNumber, sort);
			result = getEqNodeAndFunctionFactory().getOrConstructNode(tv);
			mDimensionToWeqVariableNode.put(sort, dimensionNumber, result);
		}
		return result;
	}

	public TermVariable getWeqVariableForDimension(final int dimensionNumber, final Sort sort) {
		return (TermVariable) getWeqVariableNodeForDimension(dimensionNumber, sort).getTerm();
	}


	public Set<TermVariable> getAllWeqVariables() {
		final Set<TermVariable> result = new HashSet<>();
		mDimensionToWeqVariableNode.entrySet().forEach(en -> result.add((TermVariable) en.getThird().getTerm()));
		return result;
	}

	public Set<NODE> getAllWeqNodes() {
		final Set<NODE> result = new HashSet<>();
		mDimensionToWeqVariableNode.entrySet().forEach(en -> result.add(en.getThird()));
		return result;
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> getTopDisjunctiveConstraint() {
		return getDisjunctiveConstraint(Collections.singleton(getEmptyConstraint()));
	}

	public EqConstraint<ACTION, NODE, FUNCTION> getEqConstraint(
			final WeqCongruenceClosure<ACTION, NODE, FUNCTION> newPartialArrangement) {
		if (newPartialArrangement.isInconsistent()) {
			return getBottomConstraint();
		}
		return new EqConstraint<>(newPartialArrangement, this);
	}

	public ManagedScript getMgdScript() {
		return mCsToolkit.getManagedScript();
	}

	@Override
	public String toString() {
		return this.getClass().getSimpleName();
	}
}
