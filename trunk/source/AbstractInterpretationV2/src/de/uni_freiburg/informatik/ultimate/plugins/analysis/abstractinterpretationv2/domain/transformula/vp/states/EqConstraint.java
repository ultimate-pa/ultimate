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
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 * @param <NODE>
 * @param <FUNCTION>
 */
public class EqConstraint<ACTION extends IIcfgTransition<IcfgLocation>,
		NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
		FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {

	private final CongruenceClosure<NODE, FUNCTION> mPartialArrangement;
	private final WeakEquivalenceGraph mWeakEquivalenceGraph;

	private boolean mIsFrozen;

	private final EqConstraintFactory<ACTION, NODE, FUNCTION> mFactory;
	/**
	 * The IProgramVars whose getTermVariable()-value is used in a NODE inside this constraint;
	 * computed lazily by getVariables.
	 */
	private Set<IProgramVar> mVariables;
	/**
	 * Same as mVariables, but with respect to IProgramVarOrConst, and getTerm, instead of IProgramVar and
	 * getTermVariable.
	 */
	private Set<IProgramVarOrConst> mPvocs;
	private Term mTerm;


	private final NestedMap2<Sort, Integer, NODE> mDimensionToWeqVariableNode = new NestedMap2<>();

	/**
	 * Creates an empty constraint (i.e. an EqConstraint that does not constrain anything, whose toTerm() will return
	 * "true").
	 *
	 * @param factory
	 */
	public EqConstraint(final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
		mPartialArrangement = new CongruenceClosure<>();
		mWeakEquivalenceGraph = new WeakEquivalenceGraph();
		mFactory = factory;
	}

	public EqConstraint(final CongruenceClosure<NODE, FUNCTION> cClosure, final WeakEquivalenceGraph weqGraph,
			final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
		mPartialArrangement = new CongruenceClosure<>(cClosure);
		mWeakEquivalenceGraph = new WeakEquivalenceGraph(weqGraph);
		mFactory = factory;
	}

	/**
	 * Copy constructor.
	 *
	 * @param constraint
	 */
	public EqConstraint(final EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		mPartialArrangement = new CongruenceClosure<>(constraint.mPartialArrangement);
		mWeakEquivalenceGraph = new WeakEquivalenceGraph(constraint.mWeakEquivalenceGraph);
		mFactory = constraint.mFactory;
	}

	public void freeze() {
		assert !mIsFrozen;
		mIsFrozen = true;
	}

	/**
	 * Whenever an EqConstraint becomes inconsistent, we replace it with an EqBottomConstraint.
	 * Thus this should always return false. (see also checkForContradictionMethod)
	 * @return
	 */
	public boolean isBottom() {
		assert !mPartialArrangement.isInconsistent();
		return false;
	}

	public Set<NODE> getAllNodes() {
		return mPartialArrangement.getAllElements();
	}

	public boolean reportEquality(final NODE node1, final NODE node2) {
		assert !mIsFrozen;

		boolean madeChanges = false;

		madeChanges |= mPartialArrangement.reportEquality(node1, node2);
		if (!madeChanges) {
			// if mPartialArrangement has not changed, we don't need to report to the weq graph
			return false;
		}
		return true;
	}

	void saturate() {

		final boolean changedWeqGraph = mWeakEquivalenceGraph.applyChangesInGroundPartialArrangement();
		if (!changedWeqGraph) {
			// nothing to do
			return;
		}

		while (true) {
			if (!mWeakEquivalenceGraph.hasArrayEqualities()) {
				// no weak equivalence edges' label became inconsistent (anymor), we are done
				// the result is true because the partial arrangement has changed
				return;
			}


			for (final Entry<FUNCTION, FUNCTION> aeq : mWeakEquivalenceGraph.getArrayEqualities().entrySet()) {
				mPartialArrangement.reportFunctionEquality(aeq.getKey(), aeq.getValue());
			}
			mWeakEquivalenceGraph.applyChangesInGroundPartialArrangement();
		}
	}

	public boolean reportDisequality(final NODE node1, final NODE node2) {
		assert !mIsFrozen;
		final boolean paHasChanged = mPartialArrangement.reportDisequality(node1, node2);
		if (!paHasChanged) {
			// if mPartialArrangement has not changed, we don't need to report to the weq graph
			return false;
		}
		return true;
	}

	public boolean reportFunctionEquality(final FUNCTION func1, final FUNCTION func2) {
		assert !mIsFrozen;
		final boolean paHasChanged = mPartialArrangement.reportFunctionEquality(func1, func2);
		if (!paHasChanged) {
			// if mPartialArrangement has not changed, we don't need to report to the weq graph
			return false;
		}
		return true;
	}

	public boolean reportFunctionDisequality(final FUNCTION func1, final FUNCTION func2) {
		assert !mIsFrozen;
		final boolean paHasChanged = mPartialArrangement.reportFunctionDisequality(func1, func2);
		if (!paHasChanged) {
			// if mPartialArrangement has not changed, we don't need to report to the weq graph
			return false;
		}
		return true;
	}

	public void reportWeakEquivalence(final FUNCTION array1, final FUNCTION array2,
			final List<NODE> storeIndex) {
		assert !mIsFrozen;
		mPartialArrangement.getRepresentativeAndAddFunctionIfNeeded(array1);
		mPartialArrangement.getRepresentativeAndAddFunctionIfNeeded(array2);
		mWeakEquivalenceGraph.reportWeakEquivalence(array1, array2, storeIndex);
	}

//	public boolean checkForContradiction() {
//		if (mPartialArrangement.isInconsistent()) {
//			return true;
//		}
//		TODO..
//		assert false;
//		return false;
//	}

	public boolean isFrozen() {
		return mIsFrozen;
	}

	/**
	 *
	 *
	 * TODO: this method does not fit in well, as it is not in-place but returns a fresh EqConstraint
	 *   --> perhaps move to factory..
	 *
	 * @param varsToProjectAway
	 * @return
	 */
	public EqConstraint<ACTION, NODE, FUNCTION> projectExistentially(final Collection<TermVariable> varsToProjectAway) {
		assert mIsFrozen;
		final EqConstraint<ACTION, NODE, FUNCTION> unfrozen = mFactory.unfreeze(this);

		varsToProjectAway.forEach(unfrozen::havoc);

		unfrozen.freeze();
		assert VPDomainHelpers.constraintFreeOfVars(varsToProjectAway, unfrozen,
				mFactory.getMgdScript().getScript()) :
					"resulting constraint still has at least one of the to-be-projected vars";

		return unfrozen;
	}

	private void havoc(final TermVariable var) {
		assert !mIsFrozen;
		for (final NODE elem : mPartialArrangement.getAllElements().stream()
				.filter(e -> arrayContains(e.getTerm().getFreeVars(), var)).collect(Collectors.toList())) {
			mPartialArrangement.removeElement(elem);
			mWeakEquivalenceGraph.projectElement(elem);
		}
		for (final FUNCTION func : mPartialArrangement.getAllFunctions().stream()
				.filter(f -> arrayContains(f.getTerm().getFreeVars(), var)).collect(Collectors.toList())) {
			mPartialArrangement.removeFunction(func);
			mWeakEquivalenceGraph.projectFunction(func);
		}
	}

	private <E, F extends E> boolean arrayContains(final E[] freeVars, final F var) {
		for (int i = 0; i < freeVars.length; i++) {
			if (freeVars[i].equals(var)) {
				return true;
			}
		}
		return false;
	}

	public void renameVariables(final Map<Term, Term> substitutionMapping) {
		assert !mIsFrozen;
		mPartialArrangement.transformElementsAndFunctions(
				node -> node.renameVariables(substitutionMapping),
				function -> function.renameVariables(substitutionMapping));
		mWeakEquivalenceGraph.renameVariables(substitutionMapping);
		resetCachingFields();
	}

	private void resetCachingFields() {
		mVariables = null;
		mPvocs = null;
		mTerm = null;
	}

	/**
	 *
	 * @param node1
	 * @param node2
	 * @return true iff this constraint implies that node1 and node2 are equal
	 */
	public boolean areEqual(final NODE node1, final NODE node2) {
		if (!mPartialArrangement.hasElement(node1)
		 || !mPartialArrangement.hasElement(node2)) {
			return false;
		}
		return mPartialArrangement.getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL;
	}

	/**
	 *
	 * @param node1
	 * @param node2
	 * @return true iff this constraint implies that node1 and node2 are unequal
	 */
	public boolean areUnequal(final NODE node1, final NODE node2) {
		if (!mPartialArrangement.hasElement(node1)
		 || !mPartialArrangement.hasElement(node2)) {
			return false;
		}
		return mPartialArrangement.getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL;
	}

	public boolean areEqual(final FUNCTION func1, final FUNCTION func2) {
		if (!mPartialArrangement.hasFunction(func1)
		 || !mPartialArrangement.hasFunction(func2)) {
			return false;
		}
		return mPartialArrangement.getEqualityStatus(func1, func2) == EqualityStatus.NOT_EQUAL;
	}

	public boolean areUnequal(final FUNCTION func1, final FUNCTION func2) {
		if (!mPartialArrangement.hasFunction(func1)
		 || !mPartialArrangement.hasFunction(func2)) {
			return false;
		}
		return mPartialArrangement.getEqualityStatus(func1, func2) == EqualityStatus.EQUAL;
	}

	public Term getTerm(final Script script) {
		assert mIsFrozen : "not yet frozen, term may not be final..";
		if (mTerm != null) {
			return mTerm;
		}


		final CongruenceClosure<NODE, FUNCTION> pa = mPartialArrangement;

		final List<Term> allConjuncts =  new ArrayList<>();
		allConjuncts.addAll(partialArrangementToCube(script, pa));

		final List<Term> weakEqConstraints = mWeakEquivalenceGraph.getWeakEquivalenceConstraintsAsTerms(script);
		allConjuncts.addAll(weakEqConstraints);

		final Term result= Util.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
		if (mIsFrozen) {
			mTerm = result;
		}
		return result;
	}

	private List<Term> partialArrangementToCube(final Script script, final CongruenceClosure<NODE, FUNCTION> pa) {

		final List<Term> elementEqualities = pa.getSupportingElementEqualities().entrySet().stream()
				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> elementDisequalities = pa.getElementDisequalities().entrySet().stream()
				.map(pair -> script.term("distinct", pair.getKey().getTerm(), pair.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> functionEqualities = pa.getSupportingFunctionEqualities().entrySet().stream()
				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> functionDisequalities = pa.getFunctionDisequalities().entrySet().stream()
				.map(pair -> script.term("distinct", pair.getKey().getTerm(), pair.getValue().getTerm()))
				.collect(Collectors.toList());

		final List<Term> result = new ArrayList<>(elementEqualities.size() + elementDisequalities.size()
			+ functionEqualities.size() + functionDisequalities.size());
		result.addAll(elementEqualities);
		result.addAll(elementDisequalities);
		result.addAll(functionEqualities);
		result.addAll(functionDisequalities);
		return result;
	}

	/**
	 * This only really makes sense when this constraint is in a renaming state
	 * such that the TermVariables are "normalized" to the TermVariables that
	 * are associated to IProgramVars.
	 *
	 * I.e. when it is the constraint of a EqPredicate or an EqState
	 *
	 * @return
	 */
	public Set<IProgramVar> getVariables(final IIcfgSymbolTable symbolTable) {
		if (mVariables != null) {
			return mVariables;
		}
		final Set<TermVariable> allTvs = new HashSet<>();
		mPartialArrangement.getAllElements().stream()
		.forEach(node -> allTvs.addAll(Arrays.asList(node.getTerm().getFreeVars())));

		mPartialArrangement.getAllFunctions().stream()
		.forEach(func -> allTvs.addAll(Arrays.asList(func.getTerm().getFreeVars())));

		/*
		 * note this will probably crash if this method is called on an
		 * EqConstraint that does not belong to a predicate or state
		 */
		mVariables = allTvs.stream().map(symbolTable::getProgramVar).collect(Collectors.toSet());

		assert !mVariables.stream().anyMatch(Objects::isNull);
		return mVariables;
	}

	/**
	 * Collects the Pvocs (IprogramVarOrConsts) that are mentioned in this EqConstraint by looking up the TermVariables
	 * and nullary ApplicationTerms in the symbol table.
	 *
	 * These Pvocs correspond to the Pvocs of the compacted version of an EqState that has this constraint, i.e.,
	 * only Pvocs that are actually constrained by this constraint are mentioned.
	 *
	 * We expect this to only be called when this constraint is the constraint
	 * of an EqState, thus we expect all TermVariables to correspond to an IProgramVar and all nullary ApplicationTerms
	 * to correspond to a constant that is mentioned in the symbol table.
	 *
	 * @param symbolTable
	 *
	 * @return
	 */
	public Set<IProgramVarOrConst> getPvocs(final IIcfgSymbolTable symbolTable) {
		assert mIsFrozen;
		if (mPvocs != null) {
			return mPvocs;
		}
		mPvocs = new HashSet<>();
		mPvocs.addAll(getVariables(symbolTable));

		final Set<ApplicationTerm> constants = new HashSet<>();
		mPartialArrangement.getAllElements().stream()
		.forEach(node -> constants.addAll(new ConstantFinder().findConstants(node.getTerm(), false)));
		// TODO do we need to find literals here, too?? (i.e. ConstantTerms)

		mPartialArrangement.getAllFunctions().stream()
			.forEach(func -> constants.addAll(new ConstantFinder().findConstants(func.getTerm(), false)));

		mPvocs.addAll(constants.stream().map(c -> symbolTable.getProgramConst(c)).collect(Collectors.toSet()));

		assert !mPvocs.stream().anyMatch(Objects::isNull);
		return mPvocs;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Partial arrangement:\n");
		sb.append(mPartialArrangement.toString());
		sb.append("\n");
		sb.append("Weak equivalences:\n");
		sb.append(mWeakEquivalenceGraph.toString());
		return sb.toString();

//		final List<String> allPartitionsAndRepresentativeDisequalities = new ArrayList<>();
//		String sep = "";
//		final StringBuilder sb = new StringBuilder();
//		for (final String s : allPartitionsAndRepresentativeDisequalities) {
//			sb.append(sep);
//			sep = "\n";
//			sb.append(s);
//		}
//
//		return sb.toString();
	}

	public boolean hasNode(final NODE node) {
		return mPartialArrangement.getAllElements().contains(node);
	}

	public Set<FUNCTION> getAllFunctions() {
		return mPartialArrangement.getAllFunctions();
	}

	public boolean isTop() {
		if (!mPartialArrangement.isTautological()) {
			return false;
		}
		if (!mWeakEquivalenceGraph.isEmpty()) {
			return false;
		}
		return true;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> join(final EqConstraint<ACTION, NODE, FUNCTION> other) {
		final CongruenceClosure<NODE, FUNCTION> newPartialArrangement = this.mPartialArrangement.join(
				other.mPartialArrangement);
		final WeakEquivalenceGraph newWEGraph = mWeakEquivalenceGraph.join(other.mWeakEquivalenceGraph,
				newPartialArrangement);
		final EqConstraint<ACTION, NODE, FUNCTION> res = mFactory.getEqConstraint(newPartialArrangement, newWEGraph);
		res.freeze();
		return res;
	}


	public EqConstraint<ACTION, NODE, FUNCTION> meet(final EqConstraint<ACTION, NODE, FUNCTION> other) {
		final EqConstraint<ACTION, NODE, FUNCTION>.WeakEquivalenceGraph currentWeqGraph = other.mWeakEquivalenceGraph;

		final CongruenceClosure<NODE, FUNCTION> meetPartialArrangement =
				this.mPartialArrangement.meet(other.mPartialArrangement);
		if (meetPartialArrangement.isInconsistent()) {
			return mFactory.getBottomConstraint();
		}

		final EqConstraint<ACTION, NODE, FUNCTION>.WeakEquivalenceGraph weqMeet =
					mWeakEquivalenceGraph.meet(currentWeqGraph, meetPartialArrangement);
		while (true) {

			if (!weqMeet.hasArrayEqualities()) {
				// no weak equivalence edges' label became inconsistent -- report result
				final EqConstraint<ACTION, NODE, FUNCTION> res =
						mFactory.getEqConstraint(meetPartialArrangement, weqMeet);
				res.freeze();
				return res;
			}


			for (final Entry<FUNCTION, FUNCTION> aeq : weqMeet.getArrayEqualities().entrySet()) {
				meetPartialArrangement.reportFunctionEquality(aeq.getKey(), aeq.getValue());
			}
			mWeakEquivalenceGraph.applyChangesInGroundPartialArrangement();
		}
	}


	/**
	 *
	 * @param other
	 * @return true iff this is more or equally constraining than other
	 */
	public boolean isStrongerThan(final EqConstraint<ACTION, NODE, FUNCTION> other) {
		if (!mPartialArrangement.isStrongerThan(other.mPartialArrangement)) {
			return false;
		}
		if (!mWeakEquivalenceGraph.isStrongerThan(other.mWeakEquivalenceGraph)) {
			return false;
		}
		return true;
	}

	public void addNode(final NODE nodeToAdd) {
		assert !mIsFrozen;
		mPartialArrangement.getRepresentativeAndAddElementIfNeeded(nodeToAdd);
	}

	public void addFunction(final FUNCTION func) {
		assert !mIsFrozen;
		mPartialArrangement.getRepresentativeAndAddFunctionIfNeeded(func);
	}

	private NODE getWeqVariableNodeForDimension(final int dimensionNumber, final Sort sort) {
		NODE result = mDimensionToWeqVariableNode.get(sort, dimensionNumber);
		if (result == null) {
			final TermVariable tv = mFactory.getMgdScript().constructFreshTermVariable("weq" + dimensionNumber, sort);
			result = mFactory.getEqNodeAndFunctionFactory().getOrConstructNode(tv);
			mDimensionToWeqVariableNode.put(sort, dimensionNumber, result);
		}
		return result;
	}

	private TermVariable getWeqVariableForDimension(final int dimensionNumber, final Sort sort) {
		return (TermVariable) getWeqVariableNodeForDimension(dimensionNumber, sort).getTerm();
	}

	private Set<TermVariable> getAllWeqVariables() {
		final Set<TermVariable> result = new HashSet<>();
		mDimensionToWeqVariableNode.entrySet().forEach(en -> result.add((TermVariable) en.getThird().getTerm()));
		return result;
	}

	private Set<NODE> getAllWeqNodes() {
		final Set<NODE> result = new HashSet<>();
		mDimensionToWeqVariableNode.entrySet().forEach(en -> result.add(en.getThird()));
		return result;
	}

	class WeakEquivalenceGraph {
		private final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> mWeakEquivalenceEdges;
		private final Map<FUNCTION, FUNCTION> mArrayEqualities;

		/**
		 * Constructs an empty WeakEquivalenceGraph
		 */
		public WeakEquivalenceGraph() {
			mWeakEquivalenceEdges = new HashMap<>();
			mArrayEqualities = new HashMap<>();
			assert sanityCheck();
		}

		/**
		 * Checks if any weak equivalence-edge label is inconsistent with the current mPartialArrangment.
		 * If so, it removes the edge and adds an array equality.
		 *
		 * @return true iff weak equivalence graph changed during this operation
		 */
		public boolean applyChangesInGroundPartialArrangement() {
			assert mArrayEqualities.isEmpty();
			boolean madeChanges = false;
			final HashMap<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edgesCopy =
					new HashMap<>(mWeakEquivalenceEdges);
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : edgesCopy.entrySet()) {
				if (edge.getValue().isInconsistentWith(mPartialArrangement)) {
					mWeakEquivalenceEdges.remove(edge.getKey());
					mArrayEqualities.put(edge.getKey().getOneElement(), edge.getKey().getOtherElement());
					madeChanges |= true;
				}
			}
			return madeChanges;
		}

		public void projectFunction(final FUNCTION func) {
			final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edgesCopy = new HashMap<>(mWeakEquivalenceEdges);
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : edgesCopy.entrySet()) {
				if (en.getKey().getOneElement().equals(func) || en.getKey().getOtherElement().equals(func)) {
					mWeakEquivalenceEdges.remove(en.getKey());
				} else {
					en.getValue().projectFunction(func);
				}
			}
		}

		public void projectElement(final NODE elem) {
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : mWeakEquivalenceEdges.entrySet()) {
				en.getValue().projectElement(elem);
			}
		}

		public void renameVariables(final Map<Term, Term> substitutionMapping) {
			final HashMap<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weqEdgesCopy =
					new HashMap<>(mWeakEquivalenceEdges);
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : weqEdgesCopy.entrySet()) {
				mWeakEquivalenceEdges.remove(en.getKey());

				final Doubleton<FUNCTION> newDton = new Doubleton<>(
						en.getKey().getOneElement().renameVariables(substitutionMapping),
						en.getKey().getOtherElement().renameVariables(substitutionMapping));
				en.getValue().renameVariables(substitutionMapping); //TODO : is doing it in-place a smart choice??
				mWeakEquivalenceEdges.put(newDton, en.getValue());
			}
		}

		public Map<FUNCTION, FUNCTION> getArrayEqualities() {
			assert hasArrayEqualities();
			return mArrayEqualities;
		}

		/**
		 *
		 * @param weakEquivalenceEdges caller needs to make sure that no one else has a reference to this map -- we are
		 * 		not making a copy here.
		 * @param arrayEqualities for the special case of an intermediate weq graph during the meet operation where an
		 *      edge label became "bottom"
		 */
		private WeakEquivalenceGraph(final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weakEquivalenceEdges,
				final Map<FUNCTION, FUNCTION> arrayEqualities) {
			mWeakEquivalenceEdges = weakEquivalenceEdges;
			mArrayEqualities = arrayEqualities;
		}

		/**
		 * Copy constructor
		 * @param weakEquivalenceGraph
		 */
		public WeakEquivalenceGraph(final WeakEquivalenceGraph weakEquivalenceGraph) {
			this(weakEquivalenceGraph, true);
			assert weakEquivalenceGraph.mArrayEqualities.isEmpty();
		}

		WeakEquivalenceGraph(final WeakEquivalenceGraph weqMeet, final boolean forgetArrayEqualities) {
			mArrayEqualities = forgetArrayEqualities ? new HashMap<>() : new HashMap<>(weqMeet.mArrayEqualities);
			mWeakEquivalenceEdges = new HashMap<>();
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weqEdge
					: weqMeet.mWeakEquivalenceEdges.entrySet()) {
				mWeakEquivalenceEdges.put(weqEdge.getKey(), new WeakEquivalenceEdgeLabel(weqEdge.getValue()));
			}
			assert sanityCheck();
		}

		/**
		 *
		 * @param other
		 * @param newPartialArrangement the joined partialArrangement, we need this because the edges of the the new
		 * 		Weakequivalence graph have to be between the new equivalence representatives
		 * @return
		 */
		WeakEquivalenceGraph join(final WeakEquivalenceGraph other,
				final CongruenceClosure<NODE, FUNCTION> newPartialArrangement) {
			final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> newWeakEquivalenceEdges = new HashMap<>();
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> thisWeqEdge
					: this.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther =
						other.mWeakEquivalenceEdges.get(thisWeqEdge.getKey());
				if (correspondingWeqEdgeInOther == null) {
					continue;
				}
				newWeakEquivalenceEdges.put(thisWeqEdge.getKey(),
						thisWeqEdge.getValue().union(correspondingWeqEdgeInOther));

			}
			return new WeakEquivalenceGraph(newWeakEquivalenceEdges, null);
		}

		WeakEquivalenceGraph meet(final WeakEquivalenceGraph other,
				final CongruenceClosure<NODE, FUNCTION> newPartialArrangement) {
			final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> newWeakEquivalenceEdges = new HashMap<>();
			final Map<FUNCTION, FUNCTION> newArrayEqualities = new HashMap<>();
			/*
			 * for clarity we distinguish three cases for any two nodes (n1, n2) in the weq-graph
			 *  <li> there is an edge (n1, I, n2) in this but not in other
			 *  <li> there is an edge  (n1, I, n2) in other but not in this
			 *  <li> there are edges (n1, I, n2), (n1, I', n2) in both
			 */
			// case 1
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> thisWeqEdge
					: this.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther =
						other.mWeakEquivalenceEdges.get(thisWeqEdge.getKey());
				if (correspondingWeqEdgeInOther != null) {
					// case 3 applies
					continue;
				}
				final WeakEquivalenceEdgeLabel newEdgeLabel = thisWeqEdge.getValue();
				if (newEdgeLabel.isInconsistentWith(newPartialArrangement)) {
					// edge label became inconsistent -- add a strong equivalence instead of a weak one
					newArrayEqualities.put(thisWeqEdge.getKey().getOneElement(),
							thisWeqEdge.getKey().getOtherElement());
					continue;
				}
				newWeakEquivalenceEdges.put(thisWeqEdge.getKey(), newEdgeLabel);
			}
			// case 2
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> otherWeqEdge
					: other.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInThis =
						this.mWeakEquivalenceEdges.get(otherWeqEdge.getKey());
				if (correspondingWeqEdgeInThis != null) {
					// case 3 applies
					continue;
				}
				final WeakEquivalenceEdgeLabel newEdgeLabel = otherWeqEdge.getValue();
				if (newEdgeLabel.isInconsistentWith(newPartialArrangement)) {
					// edge label became inconsistent -- add a strong equivalence instead of a weak one
					newArrayEqualities.put(otherWeqEdge.getKey().getOneElement(),
							otherWeqEdge.getKey().getOtherElement());
					continue;
				}
				newWeakEquivalenceEdges.put(otherWeqEdge.getKey(), newEdgeLabel);

			}
			// case 3
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> thisWeqEdge
					: this.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther =
						other.mWeakEquivalenceEdges.get(thisWeqEdge.getKey());
				if (correspondingWeqEdgeInOther == null) {
					// not case 3
					continue;
				}
				final WeakEquivalenceEdgeLabel newEdgeLabel = thisWeqEdge.getValue().meet(correspondingWeqEdgeInOther);
				if (newEdgeLabel.isInconsistentWith(newPartialArrangement)) {
					// edge label became inconsistent -- add a strong equivalence instead of a weak one
					newArrayEqualities.put(thisWeqEdge.getKey().getOneElement(),
							thisWeqEdge.getKey().getOtherElement());
					continue;
				}
				newWeakEquivalenceEdges.put(thisWeqEdge.getKey(), newEdgeLabel);
			}
			return new WeakEquivalenceGraph(newWeakEquivalenceEdges, newArrayEqualities);
		}

		boolean hasArrayEqualities() {
			return !mArrayEqualities.isEmpty();
		}

		/**
		 *
		 * @return true if this graph has no constraints/is tautological
		 */
		public boolean isEmpty() {
			return mWeakEquivalenceEdges.isEmpty() && !hasArrayEqualities();
		}

		/**
		 *
		 * @param func1 edge source (edge is symmetric)
		 * @param func2 edge target (edge is symmetric)
		 * @param nodes position where FUNCTIONs may differ
		 * @return
		 */
		public boolean reportWeakEquivalence(final FUNCTION func1, final FUNCTION func2, final List<NODE> nodes) {
			assert func1.getArity() == func2.getArity();
			final Doubleton<FUNCTION> sourceAndTarget = new Doubleton<FUNCTION>(func1, func2);
			WeakEquivalenceEdgeLabel edgeLabel = mWeakEquivalenceEdges.get(sourceAndTarget);
			if (edgeLabel == null) {
				edgeLabel = new WeakEquivalenceEdgeLabel(func1.getArity());
				mWeakEquivalenceEdges.put(sourceAndTarget, edgeLabel);
			}
			final List<CongruenceClosure<NODE, FUNCTION>> newConstraint = computeWeqConstraintForIndex(nodes);
			final boolean stateChanged = edgeLabel.addConstraint(newConstraint);
			return stateChanged;
		}

		/**
		 * Given a (multidimensional) index, compute the corresponding annotation for a weak equivalence edge.
		 *
		 * Example:
		 * for (i1, .., in), this should return (q1 = i1, ..., qn = in) as a list of CongruenceClosures.
		 *  (where qi is the variable returned by getWeqVariableForDimension(i))
		 *
		 * @param nodes
		 * @return
		 */
		private List<CongruenceClosure<NODE, FUNCTION>> computeWeqConstraintForIndex(final List<NODE> nodes) {
			final List<CongruenceClosure<NODE, FUNCTION>> result = new ArrayList<>(nodes.size());
			for (int i = 0; i < nodes.size(); i++) {
				final NODE ithNode = nodes.get(i);
				final CongruenceClosure<NODE, FUNCTION> newCC = new CongruenceClosure<>();
				newCC.reportEquality(getWeqVariableNodeForDimension(i, ithNode.getTerm().getSort()), ithNode);
				result.add(newCC);
			}
			return result;
		}

		/**
		 *
		 * @param func1 edge source (edge is symmetric)
		 * @param func2 edge target (edge is symmetric)
		 * @param partialArrangements partial arrangement describing where FUNCTIONs may differ
		 * @return
		 */
		public boolean reportWeakEquivalence(final FUNCTION func1, final FUNCTION func2,
				final CongruenceClosure<NODE, FUNCTION>... partialArrangements) {
			assert false;
			return false;
		}

		/**
		 *
		 * @param func1 edge source (edge is symmetric)
		 * @param func2 edge target (edge is symmetric)
		 * @param partialArrangements disjunction of partial arrangement describing where FUNCTIONs may differ
		 * @return
		 */
		public boolean reportWeakEquivalence(final FUNCTION func1, final FUNCTION func2,
				final Collection<CongruenceClosure<NODE, FUNCTION>>... partialArrangements) {
			assert false;
			return false;
		}


		public boolean isStrongerThan(final WeakEquivalenceGraph other) {
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> otherWeqEdgeAndLabel
					: other.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInThis =
						this.mWeakEquivalenceEdges.get(otherWeqEdgeAndLabel.getKey());
				if (correspondingWeqEdgeInThis == null) {
					// "other" has an edge that "this" does not -- this cannot be stronger
					return false;
				}
				// if the this-edge is strictly weaker than the other-edge, we have a counterexample
				if (!correspondingWeqEdgeInThis.isStrongerThan(otherWeqEdgeAndLabel.getValue())) {
					return false;
				}
			}
			return true;
		}

		/**
		 * Computes an implicitly conjunctive list of weak equivalence constraints. Each element in the list is the
		 * constrained induced by one weak equivalence edge in this weq graph.
		 *
		 * @param script
		 * @return
		 */
		public List<Term> getWeakEquivalenceConstraintsAsTerms(final Script script) {
			assert mArrayEqualities == null || mArrayEqualities.isEmpty();
			final List<Term> result = new ArrayList<>();
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
				final List<Term> dnfAsCubeList = new ArrayList<>();
				dnfAsCubeList.addAll(edge.getValue().toDNF(script));

				final Term arrayEquation = computeArrayEquation(script, edge.getKey().getOneElement(),
						edge.getKey().getOtherElement());
				dnfAsCubeList.add(arrayEquation);

				final Term edgeFormula = SmtUtils.quantifier(script, QuantifiedFormula.FORALL,
						computeWeqIndicesForArray(edge.getKey().getOneElement()), SmtUtils.or(script, dnfAsCubeList));
				result.add(edgeFormula);
			}
			return result;
		}

		/**
		 * For the two given arrays a, b, this computes an equation a[q1, .., qn] = b[q1, ..,qn] where qi are the
		 * implicitly quantified variables of our weak equivalences (managed by getWeqVariables for dimension).
		 * Uses the array's multidimensional sort to get the right variables.
		 *
		 * @param script
		 * @param array1
		 * @param array2
		 * @return
		 */
		private Term computeArrayEquation(final Script script, final FUNCTION array1, final FUNCTION array2) {
			assert array1.getTerm().getSort().equals(array2.getTerm().getSort());
			final List<Term> indexEntries = computeWeqIndicesForArray(array1).stream().map(tv -> (Term) tv)
					.collect(Collectors.toList());
			final ArrayIndex index = new ArrayIndex(indexEntries);

			final Term select1 = SmtUtils.multiDimensionalSelect(script, array1.getTerm(), index);
			final Term select2 = SmtUtils.multiDimensionalSelect(script, array2.getTerm(), index);

			return SmtUtils.binaryEquality(script, select1, select2);
		}

		private List<TermVariable> computeWeqIndicesForArray(final FUNCTION array1) {
			final MultiDimensionalSort mdSort = new MultiDimensionalSort(array1.getTerm().getSort());

			final List<TermVariable> indexEntries = new ArrayList<>();
			for (int i = 0; i < array1.getArity(); i++) {
				indexEntries.add(getWeqVariableForDimension(i, mdSort.getIndexSorts().get(i)));
			}
			return indexEntries;
		}

		@Override
		public String toString() {
			return mWeakEquivalenceEdges.toString();
		}


		boolean sanityCheck() {
			/*
			 * check that no weak equivalence edge contains an ELEM or FUNCTION that is not known to mPartialArrangement
			 * or is one of the special quantified variables from getVariableForDimension(..).
			 */
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
				if (!mPartialArrangement.hasFunction(edge.getKey().getOneElement())
						|| !mPartialArrangement.hasFunction(edge.getKey().getOtherElement())) {
					assert false;
					return false;
				}
				if (!mPartialArrangement.getAllElements().containsAll(
						edge.getValue().getAppearingNodes().stream()
							.filter(node -> getAllWeqNodes().contains(node)).collect(Collectors.toSet()))) {
					assert false;
					return false;
				}
				if (!mPartialArrangement.getAllFunctions().containsAll(edge.getValue().getAppearingFunctions())) {
					assert false;
					return false;
				}
			}

			/*
			 * Check that all the edges are between equivalence classes of mPartialArrangement
			 */

			/*
			 * Check that none of the edges has the same source and target (is a self-loop).
			 */
			for (final Doubleton<FUNCTION> dton : mWeakEquivalenceEdges.keySet()) {
				if (dton.getOneElement().equals(dton.getOtherElement())) {
					assert false;
					return false;
				}
			}

			/*
			 * check completeness of the graph ("triangle inequality")
			 */

			return true;
		}

		/**
		 * Represents an edge label in the weak equivalence graph.
		 * An edge label connects two arrays of the same arity(dimensionality) #a.
		 * An edge label is a tuple of length #a.
		 * Each tuple element is a set of partial arrangements. The free variables in the partial arrangements are the
		 * variables of the EqConstraint together with #a special variables that are implicitly universally quantified
		 * and range over the array positions.
		 *
		 */
		class WeakEquivalenceEdgeLabel {

			private final int mArityOfArrays;

			private final List<List<CongruenceClosure<NODE, FUNCTION>>> mLabel;

			/**
			 * Constructs an empty edge. (labeled ("true", ..., "true"))
			 */
			public WeakEquivalenceEdgeLabel(final int arity) {
				mArityOfArrays = arity;
				mLabel = new ArrayList<>();
				final List<CongruenceClosure<NODE, FUNCTION>> dimensionLabels = new ArrayList<>(arity);
				mLabel.add(dimensionLabels);
				for (int i = 0; i < arity; i++) {
					dimensionLabels.add(new CongruenceClosure<>());
				}
			}

			/**
			 * Copy constructor.
			 *
			 * @param value
			 */
			public WeakEquivalenceEdgeLabel(final WeakEquivalenceEdgeLabel value) {
				mArityOfArrays = value.mArityOfArrays;
				mLabel = new ArrayList<>(value.mLabel.size());
				for (final List<CongruenceClosure<NODE, FUNCTION>> dimLabels : value.mLabel) {
					final ArrayList<CongruenceClosure<NODE, FUNCTION>> newDimlabels = new ArrayList<>(dimLabels.size());
					mLabel.add(newDimlabels);
					for (final CongruenceClosure<NODE, FUNCTION> pa : dimLabels) {
						newDimlabels.add(new CongruenceClosure<>(pa));
					}
				}
			}

			public WeakEquivalenceEdgeLabel(final List<List<CongruenceClosure<NODE, FUNCTION>>> newLabelContents,
					final int arityOfArrays) {
				mArityOfArrays = arityOfArrays;
				mLabel = newLabelContents;
			}

			/**
			 * Computes a DNF from this label as a List of conjunctive Terms.
			 *    The disjunction has the form \/_dim \/_s pa_dim_s
			 *    I.e. it has two range dimensions:
			 *  the array's dimensions and for each of these a list of partial arrangements (like qi = x \/ qi = y)
			 *
			 * @param script
			 * @return a DNF as a List of conjunctive Terms.
			 */
			public List<Term> toDNF(final Script script) {
				final List<Term> result = new ArrayList<>();
				for (int i = 0; i < mArityOfArrays; i++) {
					final List<CongruenceClosure<NODE, FUNCTION>> dimensionPas = mLabel.get(i);
					for (final CongruenceClosure<NODE, FUNCTION> cc : dimensionPas) {
						final List<Term> cube = partialArrangementToCube(script, cc);
						final Term cubeTerm = SmtUtils.and(script, cube);
						result.add(cubeTerm);
					}
				}
				return result;
			}

			/**
			 *
			 * for every every dimension:
			 *   do a meet with the given constraint's entry for that dimension
			 *
			 *  (we conjoin the new constraint, thus have to meet every element in the dimension's set)
			 * @param newConstraint
			 * @return
			 */
			public boolean addConstraint(final List<CongruenceClosure<NODE, FUNCTION>> newConstraint) {
				for (int dim = 0; dim < mArityOfArrays; dim++) {
					final List<CongruenceClosure<NODE, FUNCTION>> newLabel = new ArrayList<>();
					for (final CongruenceClosure<NODE, FUNCTION> pa : mLabel.get(dim)) {
						newLabel.add(pa.meet(newConstraint.get(dim)));
					}
					mLabel.set(dim, newLabel);
				}
				return false;
			}

			public void renameVariables(final Map<Term, Term> substitutionMapping) {
				for (final List<CongruenceClosure<NODE, FUNCTION>> disjunct : mLabel) {
					for (final CongruenceClosure<NODE, FUNCTION> dimensionEntry : disjunct) {
						dimensionEntry.transformElementsAndFunctions(node -> node.renameVariables(substitutionMapping),
								func -> func.renameVariables(substitutionMapping));
					}
				}
			}

			/**
			 * Returns all NODEs that are used in this WeqEdgeLabel.
			 * Not including the special quantified variable's nodes.
			 * @return
			 */
			public Set<NODE> getAppearingNodes() {
				final Set<NODE> res = new HashSet<>();
				mLabel.forEach(dim -> dim.forEach(pa -> res.addAll(pa.getAllElements())));
				return res;
			}

			public Set<FUNCTION> getAppearingFunctions() {
				final Set<FUNCTION> res = new HashSet<>();
				mLabel.forEach(dim -> dim.forEach(pa -> res.addAll(pa.getAllFunctions())));
				return res;
			}

			public boolean isInconsistentWith(final CongruenceClosure<NODE, FUNCTION> newPartialArrangement) {
				// algorithmic notice: it's all a big disjunction, so we just have to look for one consistent disjunct..
				for (int dim = 0; dim < mArityOfArrays; dim++) {
					for (final CongruenceClosure<NODE, FUNCTION> pa : mLabel.get(dim)) {
						if (!pa.meet(mPartialArrangement).isInconsistent()) {
							return false;
						}
					}
				}
				return true;
			}

			public WeakEquivalenceEdgeLabel meet(final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther) {
				final List<List<CongruenceClosure<NODE, FUNCTION>>> newLabelContents = new ArrayList<>();
				for (int dim = 0; dim < mArityOfArrays; dim++) {
					final ArrayList<CongruenceClosure<NODE, FUNCTION>> newLabelForDim = new ArrayList<>();
					newLabelContents.add(newLabelForDim);

					final List<List<CongruenceClosure<NODE, FUNCTION>>> li = new ArrayList<>(2);
					li.add(mLabel.get(dim));
					li.add(correspondingWeqEdgeInOther.mLabel.get(dim));
					final List<List<CongruenceClosure<NODE, FUNCTION>>> cp = CrossProducts.crossProduct(li);
					for (final List<CongruenceClosure<NODE, FUNCTION>> pair : cp) {
						assert pair.size() == 2;
						newLabelForDim.add(pair.get(0).meet(pair.get(1)));
					}
				}
				return new WeakEquivalenceEdgeLabel(newLabelContents, mArityOfArrays);
			}

			/**
			 * rule:  A isStrongerThan B
			 *     iff
			 *   forall ai exists bi. ai subseteq bi
			 * @param value
			 * @return
			 */
			public boolean isStrongerThan(final WeakEquivalenceEdgeLabel other) {
				for (int dim = 0; dim < mArityOfArrays; dim++) {
					for (final CongruenceClosure<NODE, FUNCTION> paThis : mLabel.get(dim)) {
						boolean existsWeaker = false;
						for (final CongruenceClosure<NODE, FUNCTION> paOther : other.mLabel.get(dim)) {
							if (paThis.isStrongerThan(paOther)) {
								existsWeaker = true;
								break;
							}
						}
						if (!existsWeaker) {
							return false;
						}
					}
				}
				return true;
			}

			/**
			 * Computes a constraint which, for every dimension, has the union of the disjuncts of both input labels
			 *  (this and other).
			 * @param correspondingWeqEdgeInOther
			 * @return
			 */
			public WeakEquivalenceEdgeLabel union(final WeakEquivalenceEdgeLabel other) {
				final List<List<CongruenceClosure<NODE, FUNCTION>>> newLabelContents = new ArrayList<>();
				for (int dim = 0; dim < mArityOfArrays; dim++) {
					// using a set to eliminate duplicates
					final Set<CongruenceClosure<NODE, FUNCTION>> newPasForDimension = new HashSet<>();
					newPasForDimension.addAll(this.mLabel.get(dim));
					newPasForDimension.addAll(other.mLabel.get(dim));
					newLabelContents.add(new ArrayList<>(newPasForDimension));
				}
				return new WeakEquivalenceEdgeLabel(newLabelContents, mArityOfArrays);
			}


			public void projectElement(final NODE elem) {
				mLabel.forEach(dim -> dim.forEach(pa -> pa.removeElement(elem)));
			}

			public void projectFunction(final FUNCTION func) {
				mLabel.forEach(dim -> dim.forEach(pa -> pa.removeFunction(func)));
			}

			@Override
			public String toString() {
				return mLabel.toString();
			}
		}

	}


	class CongruenceClosureChangeTracker//<ELEM extends ICongruenceClosureElement<ELEM, FUNCTION>, FUNCTION>
			extends CongruenceClosure<NODE, FUNCTION> {

		private final HashSet<Doubleton<NODE>> mFreshElementEqualities = new HashSet<>();
		private final HashSet<Doubleton<NODE>> mFreshElementDisequalities = new HashSet<>();
		private final HashSet<Doubleton<FUNCTION>> mFreshFunctionEqualities = new HashSet<>();
		private final HashSet<Doubleton<FUNCTION>> mFreshFunctionDisequalities = new HashSet<>();
		private boolean mBecameInconsistent = false;

		public CongruenceClosureChangeTracker(final CongruenceClosure<NODE, FUNCTION> originalCc) {
			super(originalCc);
		}

		@Override
		public boolean reportFunctionEquality(final FUNCTION func1, final FUNCTION func2) {
			final boolean madeChange = super.reportFunctionEquality(func1, func2);
			if (madeChange) {
				mFreshFunctionEqualities.add(new Doubleton<FUNCTION>(func1, func2));
			}
			return madeChange;
		}

		@Override
		public boolean reportFunctionDisequality(final FUNCTION func1, final FUNCTION func2) {
			final boolean madeChange = super.reportFunctionDisequality(func1, func2);
			if (madeChange) {
				mFreshFunctionDisequalities.add(new Doubleton<FUNCTION>(func1, func2));
			}
			return madeChange;
		}

		@Override
		public boolean reportEquality(final NODE elem1, final NODE elem2) {
			final boolean madeChange = super.reportEquality(elem1, elem2);
			if (madeChange) {
				mFreshElementEqualities.add(new Doubleton<NODE>(elem1, elem2));
			}
			return madeChange;
		}

		@Override
		public boolean reportDisequality(final NODE elem1, final NODE elem2) {
			final boolean madeChange = super.reportDisequality(elem1, elem2);
			if (madeChange) {
				mFreshElementDisequalities.add(new Doubleton<NODE>(elem1, elem2));
			}
			return madeChange;
		}

		@Override
		protected boolean reportDisequalityRec(final NODE elem1, final NODE elem2) {
			final boolean madeChange = super.reportDisequality(elem1, elem2);
			if (madeChange) {
				mFreshElementDisequalities.add(new Doubleton<NODE>(elem1, elem2));
			}
			return madeChange;
		}

		@Override
		protected boolean reportEqualityRec(final NODE elem1, final NODE elem2) {
			final boolean madeChange = super.reportEquality(elem1, elem2);
			if (madeChange) {
				mFreshElementEqualities.add(new Doubleton<NODE>(elem1, elem2));
			}
			return madeChange;
		}

		@Override
		protected void updateInconsistencyStatus() {
			super.updateInconsistencyStatus();
			mBecameInconsistent |= isInconsistent();
		}

		public HashSet<Doubleton<NODE>> getFreshElementEqualities() {
			return mFreshElementEqualities;
		}

		public HashSet<Doubleton<NODE>> getFreshElementDisequalities() {
			return mFreshElementDisequalities;
		}

		public HashSet<Doubleton<FUNCTION>> getFreshFunctionEqualities() {
			return mFreshFunctionEqualities;
		}

		public HashSet<Doubleton<FUNCTION>> getFreshFunctionDisequalities() {
			return mFreshFunctionDisequalities;
		}

		public boolean isBecameInconsistent() {
			return mBecameInconsistent;
		}


	}
}
