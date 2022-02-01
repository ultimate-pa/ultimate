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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CCLiteralSetConstraints;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.SetConstraint;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 * @param <NODE>
 * @param <FUNCTION>
 */
public class EqConstraint<NODE extends IEqNodeIdentifier<NODE>> {

	private final WeqCongruenceClosure<NODE> mWeqCc;

	private boolean mIsFrozen;

	final EqConstraintFactory<NODE> mFactory;
	/**
	 * The IProgramVars whose getTermVariable()-value is used in a NODE inside this constraint; computed lazily by
	 * getVariables.
	 */
	private Set<IProgramVar> mVariables;
	/**
	 * Same as mVariables, but with respect to IProgramVarOrConst, and getTerm, instead of IProgramVar and
	 * getTermVariable.
	 */
	private Set<IProgramVarOrConst> mPvocs;
	private Term mTerm;

	private final int mId;

	public EqConstraint(final int id, final WeqCongruenceClosure<NODE> cClosure,
			final EqConstraintFactory<NODE> factory) {

		assert id != Integer.MAX_VALUE : "ran out of ids for EqConstraints";

		mId = id;
		mFactory = factory;
		mWeqCc = cClosure;
	}

	private void freezeAndDontClose() {
		assert !isInconsistent() : "use EqBottomConstraint instead!!";
		assert sanityCheck();
		assert !mIsFrozen;
		mWeqCc.freezeOmitPropagations();
		mIsFrozen = true;
	}

	/**
	 * Whenever an EqConstraint becomes inconsistent, we replace it with an EqBottomConstraint. Thus this should always
	 * return false. (see also checkForContradictionMethod)
	 *
	 * @return
	 */
	public boolean isBottom() {
		assert !isInconsistent() : "this should only be called on EqConstraints that are either consistent or an "
				+ "instance of EqBottomConstraint";
		assert !mWeqCc.isInconsistent();
		return false;
	}

	public Set<NODE> getAllNodes() {
		return mWeqCc.getAllElements();
	}

	public boolean reportEqualityInPlace(final NODE node1, final NODE node2) {
		assert !isInconsistent();
		assert !mIsFrozen;

		return mWeqCc.reportEquality(node1, node2, false);
	}

	public boolean reportDisequalityInPlace(final NODE node1, final NODE node2) {
		assert !isInconsistent();
		assert !mIsFrozen;
		final boolean paHasChanged = mWeqCc.reportDisequality(node1, node2);
		return paHasChanged;
	}

	public void reportWeakEquivalenceInPlace(final NODE array1, final NODE array2, final NODE storeIndex) {
		assert !isInconsistent();
		assert !mIsFrozen;
		mFactory.getWeqCcManager().reportWeakEquivalence(mWeqCc, array1, array2, storeIndex, true);
	}

	public boolean isFrozen() {
		assert !mIsFrozen || !isInconsistent() : "an inconsistent constraint that is not EqBottomConstraint should "
				+ "never be frozen.";
		return mIsFrozen;
	}

	public boolean isInconsistent() {
		return mWeqCc.isInconsistent();
	}

	/**
	 *
	 * @param node1
	 * @param node2
	 * @param addNodesIfNecessary
	 *            whether the nodes should be added if not present already before posing the query
	 * @return true iff this constraint implies that node1 and node2 are equal
	 */
	public boolean areEqual(final NODE node1, final NODE node2, final boolean addNodesIfNecessary) {
		if (addNodesIfNecessary) {
			final WeqCongruenceClosure<NODE> unfrozen = getWeqCcWithAddedNodes(node1, node2);
			/*
			 * TODO: would it be a good idea to keep the updated weqcc here? that would mean that the eqconstraint is
			 * somewhat mutable..
			 */
			return unfrozen.getEqualityStatus(node1, node2) == EqualityStatus.EQUAL;
		}
		if (!mWeqCc.hasElement(node1) || !mWeqCc.hasElement(node2)) {
			return false;
		}
		return mWeqCc.getEqualityStatus(node1, node2) == EqualityStatus.EQUAL;
	}

	/**
	 *
	 * @param node1
	 * @param node2
	 * @param addNodesIfNecessary
	 *            whether the nodes should be added if not present already before posing the query
	 * @return true iff this constraint implies that node1 and node2 are unequal
	 */
	public boolean areUnequal(final NODE node1, final NODE node2, final boolean addNodesIfNecessary) {
		if (addNodesIfNecessary) {
			final WeqCongruenceClosure<NODE> unfrozen = getWeqCcWithAddedNodes(node1, node2);
			/*
			 * TODO: would it be a good idea to keep the updated weqcc here? that would mean that the eqconstraint is
			 * somewhat mutable..
			 */
			return unfrozen.getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL;
		}
		if (!mWeqCc.hasElement(node1) || !mWeqCc.hasElement(node2)) {
			return false;
		}
		return mWeqCc.getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL;
	}

	private WeqCongruenceClosure<NODE> getWeqCcWithAddedNodes(final NODE node1, final NODE node2) {
		assert mWeqCc.isFrozen() : "right?..";
		final WeqCcManager<NODE> manager = mWeqCc.getManager();

		final WeqCongruenceClosure<NODE> unfrozen = manager.unfreeze(mWeqCc);
		manager.addNode(node1, unfrozen, true, false);
		manager.addNode(node2, unfrozen, true, false);
		unfrozen.freezeAndClose();
		return unfrozen;
	}

	public Term getTerm(final Script script) {
		assert mIsFrozen : "not yet frozen, term may not be final..";
		if (mTerm != null) {
			return mTerm;
		}

		final Term result = WeqCcManager.weqCcToTerm(script, mWeqCc,
				mFactory.getWeqCcManager().getNonTheoryLiteralDisequalitiesIfNecessary());
		if (mIsFrozen) {
			mTerm = result;
		}
		return result;
	}

	/**
	 * This only really makes sense when this constraint is in a renaming state such that the TermVariables are
	 * "normalized" to the TermVariables that are associated to IProgramVars.
	 *
	 * I.e. when it is the constraint of a EqPredicate or an EqState
	 *
	 * @return
	 */
	public Set<IProgramVar> getVariables(final IIcfgSymbolTable symbolTable) {
		if (mVariables != null) {
			return mVariables;
		}
		final Collection<TermVariable> allTvs = getAllTermVariables();

		/*
		 * note this will probably crash if this method is called on an EqConstraint that does not belong to a predicate
		 * or state
		 */
		mVariables = allTvs.stream().map(symbolTable::getProgramVar).collect(Collectors.toSet());

		assert !mVariables.stream().anyMatch(Objects::isNull);
		return mVariables;
	}

	/**
	 * Collects the Pvocs (IprogramVarOrConsts) that are mentioned in this EqConstraint by looking up the TermVariables
	 * and nullary ApplicationTerms in the symbol table.
	 *
	 * These Pvocs correspond to the Pvocs of the compacted version of an EqState that has this constraint, i.e., only
	 * Pvocs that are actually constrained by this constraint are mentioned.
	 *
	 * We expect this to only be called when this constraint is the constraint of an EqState, thus we expect all
	 * TermVariables to correspond to an IProgramVar and all nullary ApplicationTerms to correspond to a constant that
	 * is mentioned in the symbol table.
	 *
	 * @param symbolTable
	 *
	 * @return
	 */
	public Set<IProgramVarOrConst> getPvocs(final IIcfgSymbolTable symbolTable) {
		assert mIsFrozen;
		if (mPvocs != null) {
			assert !mPvocs.stream().anyMatch(Objects::isNull);
			return mPvocs;
		}
		mPvocs = new HashSet<>();
		mPvocs.addAll(getVariables(symbolTable));

		final Set<ApplicationTerm> constants = new HashSet<>();
		mWeqCc.getAllElements().stream()
				.forEach(node -> constants.addAll(new ConstantFinder().findConstants(node.getTerm(), false)));
		// TODO do we need to find literals here, too?? (i.e. ConstantTerms)

		mPvocs.addAll(constants.stream().map(c -> symbolTable.getProgramConst(c)).collect(Collectors.toSet()));

		assert !mPvocs.stream().anyMatch(Objects::isNull);
		return mPvocs;
	}

	public boolean isTop() {
		return mWeqCc.isTautological();
	}

	public EqConstraint<NODE> join(final EqConstraint<NODE> other) {
		if (this.isBottom()) {
			return other;
		}
		if (other.isBottom()) {
			return this;
		}
		if (this.isTop()) {
			return this;
		}
		if (other.isTop()) {
			return other;
		}
		final WeqCongruenceClosure<NODE> newPartialArrangement =
				mFactory.getWeqCcManager().join(this.mWeqCc, other.mWeqCc, true);
		final EqConstraint<NODE> res = mFactory.getEqConstraint(newPartialArrangement, true);
		return res;
	}

	/**
	 *
	 * @param other
	 * @return true iff this is more or equally constraining than other
	 */
	public boolean isStrongerThan(final EqConstraint<NODE> other) {
		return mFactory.getWeqCcManager().isStrongerThan(mWeqCc, other.mWeqCc);
	}

	/**
	 *
	 * @return
	 *
	 */
	public Collection<TermVariable> getAllTermVariables() {
		final Set<TermVariable> allTvs = new HashSet<>();
		for (final NODE node : mWeqCc.getAllElements()) {
			if (node.isMixFunction()) {
				if (node.getMixFunction1() instanceof TermVariable) {
					allTvs.add((TermVariable) node.getMixFunction1());
				}
				if (node.getMixFunction2() instanceof TermVariable) {
					allTvs.add((TermVariable) node.getMixFunction2());
				}
			} else {
				allTvs.addAll(Arrays.asList(node.getTerm().getFreeVars()));
			}
		}
		return allTvs;
	}

	boolean sanityCheck() {
		/*
		 * the weak equivalence graph may not have any array equalities at this point
		 */
		if (!mWeqCc.weqGraphFreeOfArrayEqualities()) {
			assert false;
			return false;
		}

		return mWeqCc.sanityCheck();
	}

	public Integer getStatistics(final VPStatistics stat) {
		switch (stat) {
		default:
			return mWeqCc.getStatistics(stat);
		}
	}

	@Override
	public String toString() {
		return "EqConstraint#" + mId + "\n" + mWeqCc.toString();
	}

	public String toLogString() {
		return "EqConstraint#" + mId + "\n" + mWeqCc.toLogString();
	}

	@Override
	public int hashCode() {
		return mId;
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
		final EqConstraint<?> other = (EqConstraint<?>) obj;
		if (mId != other.mId) {
			return false;
		}
		return true;
	}

	public WeqCongruenceClosure<NODE> getWeqCc() {
		return mWeqCc;
	}

	/**
	 * Sets mIsFrozen flag in this EqConstraint to true, assumes that the WeqCc inside is already frozen.
	 */
	public void superficialFreeze() {
		assert mWeqCc.isFrozen();
		mIsFrozen = true;
	}

	public void freezeIfNecessary() {
		if (!isFrozen()) {
			freezeAndDontClose();
		}
	}

	public Set<NODE> getAllLiteralNodes() {
		return mWeqCc.getAllLiterals();
	}

	public boolean isClosed() {
		return mWeqCc.isClosed();
	}

	public Set<NODE> getSetConstraintForExpression(final NODE exp) {

		final WeqCongruenceClosure<NODE> unfrozen = mFactory.getWeqCcManager().unfreezeIfNecessary(mWeqCc);

		unfrozen.addElement(exp, false);

		final CCLiteralSetConstraints<NODE> lsc = unfrozen.getCongruenceClosure().getLiteralSetConstraints();
		final Set<SetConstraint<NODE>> c = lsc.getContainsConstraint(exp);

		final Optional<SetConstraint<NODE>> cLits = c.stream().filter(sc -> sc.hasOnlyLiterals()).findFirst();

		SetConstraint<NODE> result;
		try {
			result = cLits.get();
		} catch (final NoSuchElementException nsee) {
			// no set constraint found --> return null
			return null;
		}
		assert result.hasOnlyLiterals();
		return result.getLiterals();
	}
}
