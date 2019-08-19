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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.HeapSepProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingState;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqState implements IAbstractState<EqState>, IEqualityProvidingState {

	/**
	 * The variables and constants that this state has "for the abstract interpretation"/"as an IAbstractState". Note
	 * that these should be related but need not be identical to mConstraint.getPvocs(..).
	 */
	private final Set<IProgramVarOrConst> mPvocs;

	private final EqConstraint<EqNode> mConstraint;

	private final EqStateFactory mFactory;
	private final ILogger mLogger;

	private Map<IcfgEdge, EqIntermediateState> mIntermediateStatesForOutgoinEdges;

	public EqState(final EqConstraint<EqNode> constraint,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory, final EqStateFactory eqStateFactory,
			final Set<IProgramVarOrConst> variables) {
		mConstraint = constraint;
		mFactory = eqStateFactory;
		mPvocs = Collections.unmodifiableSet(new HashSet<>(variables));
		mLogger = mFactory.getLogger();
		assert assertPvocsAreComplete(constraint);
	}

	private boolean assertPvocsAreComplete(final EqConstraint<EqNode> constraint) {
		final Set<IProgramVarOrConst> set = constraint.getPvocs(mFactory.getSymbolTable()).stream()
				.filter(pvoc -> !(pvoc instanceof IProgramOldVar))
				.filter(pvoc -> !(pvoc instanceof HeapSepProgramConst))
				.filter(pvoc -> !(pvoc instanceof BoogieConst))
				.filter(pvoc -> !mFactory.getEqConstraintFactory().getNonTheoryLiterals().contains(pvoc))
				.collect(Collectors.toSet());
		if (!mPvocs.containsAll(set)) {
			assert false;
			return false;
		}
		return true;
	}

	@Override
	public EqState addVariable(final IProgramVarOrConst variable) {
		final Set<IProgramVarOrConst> newPvocs = new HashSet<>(mPvocs);
		newPvocs.add(variable);
		return mFactory.getEqState(mConstraint, newPvocs);
	}

	@Override
	public EqState removeVariable(final IProgramVarOrConst variable) {
		return removeVariables(Collections.singleton(variable));
	}

	@Override
	public EqState addVariables(final Collection<IProgramVarOrConst> variables) {
		final Set<IProgramVarOrConst> newPvocs = new HashSet<>(mPvocs);
		newPvocs.addAll(variables);
		return mFactory.getEqState(mConstraint, newPvocs);
	}

	@Override
	public EqState removeVariables(final Collection<IProgramVarOrConst> variables) {

//		final Set<IProgramVarOrConst> variablesFiltered = variables.stream().filter(var -> var instanceof IProgramVar)
//				.collect(Collectors.toSet());

		final Set<Term> termsFromPvocs =
//				variablesFiltered.stream().map(pvoc -> pvoc.getTerm()).collect(Collectors.toSet());
				variables.stream().map(pvoc -> pvoc.getTerm()).collect(Collectors.toSet());
		final EqConstraint<EqNode> projectedConstraint =
				mFactory.getEqConstraintFactory().projectExistentially(termsFromPvocs, mConstraint, false);

		final Set<IProgramVarOrConst> newVariables = new HashSet<>(mPvocs);
		newVariables.removeAll(variables);

		return mFactory.getEqState(projectedConstraint, newVariables);
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mPvocs.contains(var);
	}

	@Override
	public EqState renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return Collections.unmodifiableSet(mPvocs);
	}

	@Override
	public EqState patch(final EqState dominator) {
		final EqState newState = this.removeVariables(dominator.getVariables());
		return newState.intersect(dominator);
	}

	@Override
	public EqState intersect(final EqState other) {
		final EqConstraint<EqNode> newConstraint =
				mFactory.getEqConstraintFactory().conjoin(this.getConstraint(), other.getConstraint(), false);

		final Set<IProgramVarOrConst> newVariables = new HashSet<>();
		newVariables.addAll(this.getVariables());
		newVariables.addAll(other.getVariables());

		// return mFactory.getEqState(newConstraint, newConstraint.getPvocs(mFactory.getSymbolTable()));
		return mFactory.getEqState(newConstraint, newVariables);
	}

	@Override
	public EqState union(final EqState other) {
		final EqConstraint<EqNode> newConstraint =
				mFactory.getEqConstraintFactory().disjoin(this.getConstraint(), other.getConstraint());

		final Set<IProgramVarOrConst> newVariables = new HashSet<>();
		newVariables.addAll(this.getVariables());
		newVariables.addAll(other.getVariables());

		return mFactory.getEqState(newConstraint, newVariables);

	}

	@Override
	public boolean isEmpty() {
		return mPvocs.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return mConstraint.isBottom();
	}

	@Override
	public boolean isEqualTo(final EqState other) {
		return this.isSubsetOf(other) == SubsetResult.EQUAL || (this.isSubsetOf(other) == SubsetResult.NON_STRICT
				&& other.isSubsetOf(this) == SubsetResult.NON_STRICT);
	}

	@Override
	public SubsetResult isSubsetOf(final EqState other) {
		if (mConstraint.isTop() && other.mConstraint.isTop()) {
			return SubsetResult.EQUAL;
		}
		if (mConstraint.isBottom() && other.mConstraint.isBottom()) {
			return SubsetResult.EQUAL;
		}
		if (mConstraint.isBottom()) {
			// we know from the case above that other.mConstraint != bottom
			return SubsetResult.STRICT;
		}
		if (other.mConstraint.isTop()) {
			// we know from the case above that !mConstraint.isTop()
			return SubsetResult.STRICT;
		}

		if (this.mConstraint.isStrongerThan(other.mConstraint)) {
			return SubsetResult.NON_STRICT;
		} else {
			return SubsetResult.NONE;
		}
	}

	@Override
	public EqState compact() {
		return mFactory.getEqState(mConstraint, mConstraint.getPvocs(mFactory.getSymbolTable()));
	}

	@Override
	public Term getTerm(final Script script) {
		return mConstraint.getTerm(script);
	}

	@Override
	public String toLogString() {
		return mPvocs.toString() + "\n" + mConstraint.toLogString();
	}

	@Override
	public String toString() {
		return mPvocs.toString() + "\n" + mConstraint.toString();
	}

	public EqConstraint<EqNode> getConstraint() {
		return mConstraint;
	}

	public EqPredicate toEqPredicate() {
		return mFactory.stateToPredicate(this);
	}



	public boolean areUnequal(final EqNode node1, final EqNode node2, final boolean addNodesBeforeAnsweringQuery) {
		return mConstraint.areUnequal(node1, node2, addNodesBeforeAnsweringQuery);
	}

	@Override
	public boolean areEqual(final Term term1, final Term term2) {
		final boolean addNodesIfNecessary  = mFactory.getVpDomainSettings().isAddNodesBeforeAnsweringQuery();

		EqNode node1 = mFactory.getEqNodeAndFunctionFactory().getExistingNode(term1);
		EqNode node2 = mFactory.getEqNodeAndFunctionFactory().getExistingNode(term2);

		if (node1 == null && !addNodesIfNecessary) {
			mLogger.debug("areEqual request: Term " + term1 + " is not known to this EqState, returning false");
			return false;
		} else if (node1 == null && addNodesIfNecessary) {
			node1 = mFactory.getEqNodeAndFunctionFactory().getOrConstructNode(term1);
		}
		if (node2 == null && !addNodesIfNecessary) {
			mLogger.debug("areEqual request: Term " + term2 + " is not known to this EqState, returning false");
			return false;
		} else if (node2 == null && addNodesIfNecessary) {
			node2 = mFactory.getEqNodeAndFunctionFactory().getOrConstructNode(term2);
		}
		return mConstraint.areEqual(node1, node2, addNodesIfNecessary);
	}

	@Override
	public boolean areUnequal(final Term term1, final Term term2) {
		final boolean addNodesIfNecessary  = mFactory.getVpDomainSettings().isAddNodesBeforeAnsweringQuery();

		EqNode node1 = mFactory.getEqNodeAndFunctionFactory().getExistingNode(term1);
		EqNode node2 = mFactory.getEqNodeAndFunctionFactory().getExistingNode(term2);

		if (node1 == null && !addNodesIfNecessary) {
			mLogger.debug("areUnequal request: Term " + term1 + " is not known to this EqState, returning false");
			return false;
		} else if (node1 == null && addNodesIfNecessary) {
			node1 = mFactory.getEqNodeAndFunctionFactory().getOrConstructNode(term1);
		}
		if (node2 == null && !addNodesIfNecessary) {
			mLogger.debug("areUnequal request: Term " + term2 + " is not known to this EqState, returning false");
			return false;
		} else if (node2 == null && addNodesIfNecessary) {
			node2 = mFactory.getEqNodeAndFunctionFactory().getOrConstructNode(term2);
		}
		return mConstraint.areUnequal(node1, node2, addNodesIfNecessary);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mConstraint == null) ? 0 : mConstraint.hashCode());
		result = prime * result + ((mPvocs == null) ? 0 : mPvocs.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final EqState other = (EqState) obj;
		if (mConstraint == null) {
			if (other.mConstraint != null) {
				return false;
			}
		} else if (!mConstraint.equals(other.mConstraint)) {
			return false;
		}
		if (mPvocs == null) {
			if (other.mPvocs != null) {
				return false;
			}
		} else if (!mPvocs.equals(other.mPvocs)) {
			return false;
		}
		return true;
	}

	@Override
	public IEqualityProvidingState join(final IEqualityProvidingState other) {
		return union((EqState) other);
	}

	public EqIntermediateState getIntermediateStateForOutgoingEdge(final IcfgEdge edge) {
		if (mIntermediateStatesForOutgoinEdges == null) {
			mIntermediateStatesForOutgoinEdges = new HashMap<>();
		}

		/*
		 * TODO
		 *  - rename pre-state to edge-naming
		 *  - close conjunction
		 */
		final Map<Term, Term> subsForPred = getSubstitutionForPredecessor(edge.getTransformula());

		EqIntermediateState result = mIntermediateStatesForOutgoinEdges.get(edge);
		if (result == null) {
			final TransFormulaConverterCache tfConverter = mFactory.getTransformulaConverter();

			final EqTransitionRelation transRel =
					tfConverter.getTransitionRelationForTransformula(edge.getTransformula());

			final EqConstraintFactory<EqNode> constraintFac = mFactory.getEqConstraintFactory();

//			final List<EqDisjunctiveConstraint<EqNode>> bothConstraints = Arrays.asList(new EqDisjunctiveConstraint<EqNode>[] {
//					constraintFac.getDisjunctiveConstraint(Collections.singleton(mConstraint)),
//					transRel.getEqConstraint() });
			final List<EqDisjunctiveConstraint<EqNode>> bothConstraints = new ArrayList<>();

			final EqDisjunctiveConstraint<EqNode> predRenamed =
					constraintFac.renameVariables(
							constraintFac.getDisjunctiveConstraint(
									Collections.singleton(mConstraint)), subsForPred);

			bothConstraints.add(predRenamed);
			bothConstraints.add(transRel.getEqConstraint());

			final EqDisjunctiveConstraint<EqNode> resNotClosed = constraintFac.conjoinDisjunctiveConstraints(bothConstraints);
			final EqDisjunctiveConstraint<EqNode> res = constraintFac.closeIfNecessary(resNotClosed);
			result = new EqIntermediateState(res);
		}
		return result;
	}

	private Map<Term, Term> getSubstitutionForPredecessor(final TransFormula transRel) {
//		final Set<TermVariable> varsToProject = new HashSet<>();
//		final IValueConstruction<IProgramVar, TermVariable> substituentConstruction =
//				new IValueConstruction<IProgramVar, TermVariable>() {
//
//					@Override
//					public TermVariable constructValue(final IProgramVar pv) {
//						throw new AssertionError();
////						final TermVariable result = constructFreshTermVariable(mMgdScript, pv);
////						varsToProject.add(result);
////						return result;
//					}
//
//				};
//		final ConstructionCache<IProgramVar, TermVariable> termVariablesForPredecessor =
//				new ConstructionCache<>(substituentConstruction);

//		final Map<Term, Term> substitutionForTransFormula = new HashMap<>();
		final Map<Term, Term> substitutionForPredecessor = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : transRel.getInVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
//			if (entry.getValue() == transRel.getOutVars().get(pv)) {
//				// special case, variable unchanged will be renamed when
//				// considering outVars
//			} else {
//				final TermVariable substituent = termVariablesForPredecessor.getOrConstruct(pv);
//				substitutionForTransFormula.put(entry.getValue(), substituent);
//				if (p.getVars().contains(pv)) {
				if (this.getVariables().contains(pv)) {
//					substitutionForPredecessor.put(pv.getTermVariable(), substituent);
					substitutionForPredecessor.put(pv.getTermVariable(), entry.getValue());
				}
//			}
		}

//		for (final Entry<IProgramVar, TermVariable> entry : transRel.getOutVars().entrySet()) {
//			substitutionForTransFormula.put(entry.getValue(), entry.getKey().getTermVariable());
//			if (!transRel.getInVars().containsKey(entry.getKey()) && p.getVars().contains(entry.getKey())) {
//			if (!transRel.getInVars().containsKey(entry.getKey()) && this.getVariables().contains(entry.getKey())) {
//			if (this.getVariables().contains(entry.getKey())) {
//				final TermVariable substituent = termVariablesForPredecessor.getOrConstruct(entry.getKey());
//				substitutionForPredecessor.put(entry.getKey().getTermVariable(), substituent);
//				substitutionForPredecessor.put(entry.getKey().getTermVariable(), entry.getValue());
//			}
//		}
		return substitutionForPredecessor;
	}

//	/**
//	 * Note that an EqState is a bad IEqualityProvidingIntermediateState because it does not contain information on any
//	 * auxVar.
//	 * TODO
//	 */
//	@Override
//	public IEqualityProvidingIntermediateState join(final IEqualityProvidingIntermediateState other) {
//		return union((EqState) other);
//	}

}
