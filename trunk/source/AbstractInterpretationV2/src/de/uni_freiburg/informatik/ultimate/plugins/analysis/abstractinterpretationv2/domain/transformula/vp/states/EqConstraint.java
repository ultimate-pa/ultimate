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
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;

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

	public void reportEquality(final NODE node1, final NODE node2) {
		mPartialArrangement.reportEquality(node1, node2);
		mWeakEquivalenceGraph.reportGroundEquality(node1, node2);
	}

	public void reportDisequality(final NODE node1, final NODE node2) {
		mPartialArrangement.reportDisequality(node1, node2);
		mWeakEquivalenceGraph.reportGroundDisequality(node1, node2);
	}

	public void reportFunctionEquality(final FUNCTION func1, final FUNCTION func2) {
		mPartialArrangement.reportFunctionEquality(func1, func2);
		mWeakEquivalenceGraph.reportGroundFunctionEquality(func1, func2);
	}

	public void reportFunctionDisequality(final FUNCTION func1, final FUNCTION func2) {
		mPartialArrangement.reportFunctionDisequality(func1, func2);
		mWeakEquivalenceGraph.reportGroundFunctionDisequality(func1, func2);
	}

	public void reportWeakEquivalence(final FUNCTION array1, final FUNCTION array2,
			final List<NODE> storeIndex) {
		mWeakEquivalenceGraph.reportWeakEquivalence(array1, array2, storeIndex);
	}

	public boolean checkForContradiction() {
		if (mPartialArrangement.isInconsistent()) {
			return true;
		}
		// TODO..
		assert false;
		return false;
	}

	public boolean isFrozen() {
		return mIsFrozen;
	}

	/**
	 *
	 *
	 * TDO: should we also remove the nodes that we project, here?? edit: yes,
	 * havoc does remove the nodes
	 *
	 * @param varsToProjectAway
	 * @return
	 */
	public EqConstraint<ACTION, NODE, FUNCTION> projectExistentially(final Collection<TermVariable> varsToProjectAway) {
		final EqConstraint<ACTION, NODE, FUNCTION> unfrozen = mFactory.unfreeze(this);

		varsToProjectAway.forEach(unfrozen::havoc);

		unfrozen.freeze();
		assert VPDomainHelpers.constraintFreeOfVars(varsToProjectAway, unfrozen,
				mFactory.getEqNodeAndFunctionFactory().getScript().getScript()) :
					"resulting constraint still has at least one of the to-be-projected vars";

		return unfrozen;
	}

	private void havoc(final TermVariable var) {
		for (final NODE elem : mPartialArrangement.getAllElements().stream()
				.filter(e -> arrayContains(e.getTerm().getFreeVars(), var)).collect(Collectors.toList())) {
			mPartialArrangement.removeElement(elem);
		}
		for (final FUNCTION func : mPartialArrangement.getAllFunctions().stream()
				.filter(f -> arrayContains(f.getTerm().getFreeVars(), var)).collect(Collectors.toList())) {
			mPartialArrangement.removeFunction(func);
		}

//		mPartialArrangement.getAllElements().stream()
//			.filter(elem -> arrayContains(elem.getTerm().getFreeVars(), var))
//			.forEach(mPartialArrangement::removeElement);
//		mPartialArrangement.getAllFunctions().stream()
//			.filter(func -> arrayContains(func.getTerm().getFreeVars(), var))
//			.forEach(mPartialArrangement::removeFunction);
		mWeakEquivalenceGraph.havocVar(var);
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
	 * @return true iff this constraint says "node1 and node2 must be equal"
	 */
	public boolean areEqual(final NODE node1, final NODE node2) {
		mPartialArrangement.getRepresentativeAndAddElementIfNeeded(node1);
		mPartialArrangement.getRepresentativeAndAddElementIfNeeded(node2);
		return mPartialArrangement.getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL;
	}

	/**
	 *
	 * @param node1
	 * @param node2
	 * @return true iff this constraint says "node1 and node2 must be unequal"
	 */
	public boolean areUnequal(final NODE node1, final NODE node2) {
		mPartialArrangement.getRepresentativeAndAddElementIfNeeded(node1);
		mPartialArrangement.getRepresentativeAndAddElementIfNeeded(node2);
		return mPartialArrangement.getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL;
	}

	public Term getTerm(final Script script) {
		assert mIsFrozen : "not yet frozen, term may not be final..";
		if (mTerm != null) {
			return mTerm;
		}
		final List<Term> elementEqualities = mPartialArrangement.getSupportingElementEqualities().entrySet().stream()
				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> elementDisequalities = mPartialArrangement.getElementDisequalities().entrySet().stream()
				.map(pair -> script.term("distinct", pair.getKey().getTerm(), pair.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> functionEqualities = mPartialArrangement.getSupportingFunctionEqualities().entrySet().stream()
				.map(en -> script.term("=", en.getKey().getTerm(), en.getValue().getTerm()))
				.collect(Collectors.toList());
		final List<Term> functionDisequalities = mPartialArrangement.getFunctionDisequalities().entrySet().stream()
				.map(pair -> script.term("distinct", pair.getKey().getTerm(), pair.getValue().getTerm()))
				.collect(Collectors.toList());

		final List<Term> weakEqConstraints = mWeakEquivalenceGraph.getWeakEquivalenceConstraintsAsTerms(script);

		final List<Term> allConjuncts = new ArrayList<>();
		allConjuncts.addAll(elementEqualities);
		allConjuncts.addAll(elementDisequalities);
		allConjuncts.addAll(functionEqualities);
		allConjuncts.addAll(functionDisequalities);
		allConjuncts.addAll(weakEqConstraints);

		final Term result= Util.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
		if (mIsFrozen) {
			mTerm = result;
		}
		return result;
	}

	public boolean areEqual(final FUNCTION func1, final FUNCTION func2) {
		return mPartialArrangement.getEqualityStatus(func1, func2) == EqualityStatus.NOT_EQUAL;
	}

	public boolean areUnequal(final FUNCTION func1, final FUNCTION func2) {
		return mPartialArrangement.getEqualityStatus(func1, func2) == EqualityStatus.EQUAL;
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
		mVariables = allTvs.stream().map(tv -> symbolTable.getProgramVar(tv)).collect(Collectors.toSet());

		assert !mVariables.stream().anyMatch(var -> var == null);
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

		assert !mPvocs.stream().anyMatch(pvoc -> pvoc == null);
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

		CongruenceClosure<NODE, FUNCTION> meetPartialArrangement =
				this.mPartialArrangement.meet(other.mPartialArrangement);
		if (meetPartialArrangement.isInconsistent()) {
			return mFactory.getBottomConstraint();
		}

		EqConstraint<ACTION, NODE, FUNCTION>.WeakEquivalenceGraph weqMeet =
					mWeakEquivalenceGraph.meet(currentWeqGraph, meetPartialArrangement);
		while (true) {

			if (!weqMeet.hasArrayEqualities()) {
				// no weak equivalence edges' label became inconsistent -- report result
				final EqConstraint<ACTION, NODE, FUNCTION> res =
						mFactory.getEqConstraint(meetPartialArrangement, weqMeet);
				res.freeze();
				return res;
			}

			final CongruenceClosureChangeTracker mpaChangeTracker =
					new CongruenceClosureChangeTracker(meetPartialArrangement);
			for (final Entry<FUNCTION, FUNCTION> aeq : weqMeet.getArrayEqualities().entrySet()) {
				mpaChangeTracker.reportFunctionEquality(aeq.getKey(), aeq.getValue());

				if (mpaChangeTracker.isBecameInconsistent()) {
					return mFactory.getBottomConstraint();
				}
			}
			weqMeet = mpaChangeTracker.reportChangesToWeakEquivalenceGraph(weqMeet);
			meetPartialArrangement = new CongruenceClosure<>(mpaChangeTracker);
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


	@Deprecated
	public void removeFunction(final FUNCTION funcToBeHavocced) {
		// TODO Auto-generated method stub

	}

	@Deprecated
	public void removeNode(final NODE nodeToBeHavocced) {
		// TODO Auto-generated method stub

	}

	@Deprecated
	public void addToAllNodes(final NODE node) {
		// TODO Auto-generated method stub

	}

	public void addNode(final NODE nodeToAdd) {
		mPartialArrangement.getRepresentativeAndAddElementIfNeeded(nodeToAdd);
	}

	public void addFunction(final FUNCTION func) {
		mPartialArrangement.getRepresentativeAndAddFunctionIfNeeded(func);

	}

	private TermVariable getWeqVariableForDimension(final int dimensionNumber) {
		assert false; //TODO
		return null;
	}


	class WeakEquivalenceGraph {
		private final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> mWeakEquivalenceEdges;
		private final Map<FUNCTION, FUNCTION> mArrayEqualties;

		/**
		 * Constructs an empty WeakEquivalenceGraph
		 */
		public WeakEquivalenceGraph() {
			mWeakEquivalenceEdges = new HashMap<>();
			mArrayEqualties = null;
			assert sanityCheck();
		}

		public void renameVariables(final Map<Term, Term> substitutionMapping) {
			// TODO Auto-generated method stub

		}

		public void havocVar(final TermVariable var) {
			// TODO Auto-generated method stub

		}

		public Map<FUNCTION, FUNCTION> getArrayEqualities() {
			assert hasArrayEqualities();
			return mArrayEqualties;
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
			mArrayEqualties = arrayEqualities;
		}

		/**
		 * Copy constructor
		 * @param weakEquivalenceGraph
		 */
		public WeakEquivalenceGraph(final WeakEquivalenceGraph weakEquivalenceGraph) {
			this(weakEquivalenceGraph, true);
			assert weakEquivalenceGraph.mArrayEqualties == null;
		}

		WeakEquivalenceGraph(final WeakEquivalenceGraph weqMeet, final boolean forgetArrayEqualities) {
			mArrayEqualties = forgetArrayEqualities ? null : new HashMap<>(weqMeet.mArrayEqualties);
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
			return mArrayEqualties != null;
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
			return false;
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

		public void reportGroundEquality(final NODE node1, final NODE node2) {
			// TODO Auto-generated method stub

		}

		public void reportGroundDisequality(final NODE node1, final NODE node2) {
			// TODO Auto-generated method stub

		}

		public void reportGroundFunctionEquality(final FUNCTION func1, final FUNCTION func2) {
			// TODO Auto-generated method stub

		}

		public void reportGroundFunctionDisequality(final FUNCTION func1, final FUNCTION func2) {
			// TODO Auto-generated method stub

		}

		public List<Term> getWeakEquivalenceConstraintsAsTerms(final Script script) {
			// TODO Auto-generated method stub
			return new ArrayList<>();
		}

		boolean sanityCheck() {
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
			 * check completeness of the graph ("triangle inequation")
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

			int mArityOfArrays;

			List<List<CongruenceClosure<NODE, FUNCTION>>> mLabel;

			/**
			 * Copy constructor.
			 *
			 * @param value
			 */
			public WeakEquivalenceEdgeLabel(
					final EqConstraint<ACTION, NODE, FUNCTION>.WeakEquivalenceGraph.WeakEquivalenceEdgeLabel value) {
				// TODO Auto-generated constructor stub
			}

			public boolean isInconsistentWith(final CongruenceClosure<NODE, FUNCTION> newPartialArrangement) {
				// TODO Auto-generated method stub
				return false;
			}

			public EqConstraint<ACTION, NODE, FUNCTION>.WeakEquivalenceGraph.WeakEquivalenceEdgeLabel meet(
					final EqConstraint<ACTION, NODE, FUNCTION>.WeakEquivalenceGraph.WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther) {
				// TODO Auto-generated method stub
				return null;
			}

			public boolean isStrongerThan(
					final EqConstraint<ACTION, NODE, FUNCTION>.WeakEquivalenceGraph.WeakEquivalenceEdgeLabel value) {
				// TODO Auto-generated method stub
				return false;
			}

			public WeakEquivalenceEdgeLabel union(final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther) {
				// TODO Auto-generated method stub
				return null;
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

		/**
		 * <li> make a copy of the input, reset the array equalities
		 * <li> patch all (dis)equalities stored in this CCTracker into the new weqGraph
		 * <li> return the new weqGraph (it may contain arrayEqualities again, but only fresh ones..)
		 *
		 * @param input
		 * @return
		 */
		public WeakEquivalenceGraph reportChangesToWeakEquivalenceGraph(final WeakEquivalenceGraph input) {
			final WeakEquivalenceGraph result = new WeakEquivalenceGraph(input, true);
			mFreshElementDisequalities.stream().forEach(dton -> result.reportGroundDisequality(dton.getOneElement(),
					dton.getOtherElement()));
			mFreshElementEqualities.stream().forEach(dton -> result.reportGroundEquality(dton.getOneElement(),
					dton.getOtherElement()));
			mFreshFunctionDisequalities.stream().forEach(dton -> result.reportGroundFunctionDisequality(
					dton.getOneElement(), dton.getOtherElement()));
			mFreshFunctionEqualities.stream().forEach(dton -> result.reportGroundFunctionEquality(dton.getOneElement(),
					dton.getOtherElement()));
			return result;
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
