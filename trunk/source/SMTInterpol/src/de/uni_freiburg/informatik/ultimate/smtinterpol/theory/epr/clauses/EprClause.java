/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

/**
 * Represents a clause that is only known to the EprTheory.
 * This means that the clause typically contains at least one free
 * (implicitly forall-quantified) variable -- exceptions, i.e. ground EprClauses may occur through
 * factoring or resolution.
 *
 * @author Alexander Nutz
 */
public class EprClause {

	private final static int DAWG_FALSE = -1;
	private final static int DAWG_TRUE = -2;
	private final static int DAWG_UNKNOWN = -3;

	/**
	 * The literals in this clause, expressed as Literals (the type that the DPLLEngine knows..).
	 */
	private final List<Literal> mDpllLiterals;

	private final EprTheory mEprTheory;
	private final DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;

	private DawgState<ApplicationTerm, Integer> mDawg;

	private final List<ClauseLiteral> mLiterals;

	/**
	 * Since the introduction of equality reflexivity clauses, we want to support EprClauses that are in fact ground.
	 */
	private final boolean mIsGround;

	/**
	 * Stores the variables occurring in this clause in the order determined by the HashMap mVariableToClauseLitToPositions
	 */
	private final SortedSet<TermVariable> mVariables;

	/**
	 * If this flag is true, the value of mEprClauseState can be relied on.
	 * Otherwise the state must be recomputed.
	 */
	boolean mClauseStateIsDirty = true;

	/**
	 * The current fulfillment state of this epr clause
	 */
	private EprClauseState mEprClauseState;

	private DawgState<ApplicationTerm, Boolean> mConflictPoints;

	private UnitPropagationData mUnitPropagationData;

	private boolean mHasBeenDisposed = false;

	public EprClause(final Set<Literal> lits, final EprTheory eprTheory) {
		mDpllLiterals = new ArrayList<>(lits);
		mEprTheory = eprTheory;
		mDawgFactory = eprTheory.getDawgFactory();

		// set up the clause..
		final TreeSet<TermVariable> variables = new TreeSet<>(EprHelpers.getColumnNamesComparator());
		for (final Literal lit : lits) {
			variables.addAll(Arrays.asList(lit.getAtom().getSMTFormula(mEprTheory.getTheory()).getFreeVars()));
		}
		mVariables = variables;
		mLiterals = Collections.unmodifiableList(createClauseLiterals(lits));

		mIsGround = mVariables.isEmpty();
	}

	/**
	 * Set up the clause in terms of our Epr data structures.
	 * Fills the fields mVariableToClauseLitPositionsTemp and mLiteralsTemp.
	 *
	 * TODOs:
	 *  - detect tautologies
	 *  - detect duplicate literals
	 *
	 * @param lits The (DPLL) literals that this clause is created from.
	 * @return
	 * @return
	 */
	private List<ClauseLiteral> createClauseLiterals(final Set<Literal> lits) {

		final List<ClauseLiteral> literals = new ArrayList<>(lits.size());

//		Set<EprQuantifiedEqualityAtom> quantifiedEqualities = new HashSet<EprQuantifiedEqualityAtom>();

		for (final Literal l : lits) {
			final boolean polarity = l.getSign() == 1;
			final DPLLAtom atom = l.getAtom();

			if (atom instanceof EprQuantifiedPredicateAtom
					|| atom instanceof EprQuantifiedEqualityAtom) {
				final EprQuantifiedPredicateAtom eqpa = (EprQuantifiedPredicateAtom) atom;

				final ClauseEprQuantifiedLiteral newL = new ClauseEprQuantifiedLiteral(
						polarity, eqpa, this, mEprTheory);
				literals.add(newL);
				eqpa.getEprPredicate().addQuantifiedOccurence(newL, this);

				continue;
			} else if (atom instanceof EprGroundPredicateAtom) {
				final EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) atom;
				final ClauseEprGroundLiteral newL = new ClauseEprGroundLiteral(
						polarity, egpa, this, mEprTheory);
				literals.add(newL);
				egpa.getEprPredicate().addGroundOccurence(newL, this);
				continue;
//			} else if (atom instanceof EprQuantifiedEqualityAtom) {
//
//				todo

//				// quantified equalities we don't add to the clause literals but
//				// just collect them for adding exceptions to the other quantified
//				// clause literals later
//				assert atom == l : "should have been eliminated by destructive equality reasoning";
//				quantifiedEqualities.add((EprQuantifiedEqualityAtom) atom);
//				continue;
			} else if (atom instanceof EprGroundEqualityAtom) {
				assert false : "do we really have this case?";
				continue;
//			} else if (atom instanceof CCEquality) {
//				(distinction form DPLLAtom does not seem necessary)
//				continue;
			} else {
				// atom is a "normal" Atom from the DPLLEngine
				literals.add(
						new ClauseDpllLiteral(polarity, atom, this, mEprTheory));
				continue;
			}
		}

//		for (ClauseLiteral cl : literals) {
//			if (cl instanceof ClauseEprQuantifiedLiteral) {
//				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
//				// update all quantified predicate atoms according to the quantified equalities
//				// by excluding the corresponding points in their dawgs
//				ceql.addExceptions(quantifiedEqualities);
//			}
//		}

//		assert literals.size() == mDpllLiterals.size() - quantifiedEqualities.size();

		return literals;
	}

	/**
	 * Removes the traces of the clause in the data structures that link to it.
	 * The application I can think of now is a pop command.
	 */
	public void disposeOfClause() {
		assert !mHasBeenDisposed;
		for (final ClauseLiteral cl : mLiterals) {
			if (cl instanceof ClauseEprLiteral) {
				final ClauseEprLiteral cel = (ClauseEprLiteral) cl;
				cel.getEprPredicate().notifyAboutClauseDisposal(this);
			}
		}
		mHasBeenDisposed = true;
	}

	public void backtrackStateWrtDecideStackLiteral(final DecideStackLiteral dsl) {
		mClauseStateIsDirty = true;
	}

	/**
	 * Checks if, in the current decide state, this EprClause is
	 *  a) a conflict clause or
	 *  b) a unit clause
	 * .. on at least one grounding.
	 *
	 * TODO: this is a rather naive implementation
	 *   --> can we do something similar to two-watchers??
	 *   --> other plan: having a multi-valued dawg that count how many literals are fulfillable
	 *       for each point
	 *
	 * @return a) something that characterized the conflict (TODO: what excactly?) or
	 *         b) a unit literal for propagation (may be ground or not)
	 *         null if it is neither
	 */
	private EprClauseState determineClauseState() {
		DawgState<ApplicationTerm, Integer> myDawg =
				mDawgFactory.createConstantDawg(getVariables(), DAWG_FALSE);

		boolean isDirty = mEprClauseState == null;
		for (final ClauseLiteral cl : getLiterals()) {
			if (cl.isDirty()) {
				isDirty = true;
			}
		}
		if (!isDirty) {
			return mEprClauseState;
		}

		for (int i = 0; i < getLiterals().size(); i++) {
			final int litNr = i;
			final BiFunction<Integer, EprTheory.TriBool, Integer> clauseMerger =
					((status, tri) -> tri == EprTheory.TriBool.TRUE ? DAWG_TRUE
							: tri == EprTheory.TriBool.FALSE ? status
									: status == DAWG_FALSE ? litNr : status == DAWG_TRUE ? DAWG_TRUE : DAWG_UNKNOWN);
			myDawg = mDawgFactory.createProduct(myDawg, getLiterals().get(i).getDawg(), clauseMerger);
			assert myDawg.isTotal();
			if (DawgFactory.isConstantValue(myDawg, DAWG_TRUE)) {
				mEprClauseState = EprClauseState.Fulfilled;
				return mEprClauseState;
			}
		}
		mDawg = myDawg;
		mConflictPoints = mDawgFactory.createMapped(myDawg, i -> i == DAWG_FALSE);
		if (!DawgFactory.isEmpty(mConflictPoints)) {
			mEprClauseState = EprClauseState.Conflict;
		} else if (!DawgFactory.isEmpty(mDawgFactory.createMapped(myDawg, i -> i >= 0))) {
			mUnitPropagationData = new UnitPropagationData(this, myDawg, mDawgFactory);
			mEprClauseState = EprClauseState.Unit;
		} else {
			mEprClauseState = EprClauseState.Normal;
		}
		return mEprClauseState;
	}

	public SortedSet<TermVariable> getVariables() {
		return mVariables;
	}

	public int getVariablePos(final TermVariable variable) {
		int index = 0;
		for (final TermVariable tv : mVariables) {
			if (tv == variable) {
				return index;
			}
			index++;
		}
		throw new NoSuchElementException();
	}

	public UnitPropagationData getUnitPropagationData() {
		assert mUnitPropagationData != null;
		final UnitPropagationData result = mUnitPropagationData;
		return result;
	}

	public boolean isUnit() {
		assert !mHasBeenDisposed;
		return determineClauseState() == EprClauseState.Unit;
	}

	public boolean isConflict() {
		assert !mHasBeenDisposed;
		return determineClauseState() == EprClauseState.Conflict;
	}

	public DawgState<ApplicationTerm, Boolean> getConflictPoints() {
		assert isConflict();
		assert mConflictPoints != null : "this should have been set somewhere..";
		return mConflictPoints;
	}

	public DawgState<ApplicationTerm, Boolean> getUndecidedPoints() {
		return mDawgFactory.createMapped(mDawg, i -> i == DAWG_UNKNOWN);
	}

	public List<ClauseLiteral> getLiterals() {
		assert !mHasBeenDisposed;
		return mLiterals;
	}

	public List<Literal[]> computeAllGroundings(final List<TTSubstitution> allInstantiations) {
		final ArrayList<Literal[]> result = new ArrayList<>();
		for (final TTSubstitution sub : allInstantiations) {
			final ArrayList<Literal> groundInstList = getSubstitutedLiterals(sub);
			result.add(groundInstList.toArray(new Literal[groundInstList.size()]));
		}

		return result;
	}

	public List<Literal[]> computeAllGroundings(final HashSet<ApplicationTerm> constants) {

		final List<TTSubstitution> allInstantiations =
				EprHelpers.getAllInstantiations(getVariables(), constants);

		return computeAllGroundings(allInstantiations);
	}

	protected ArrayList<Literal> getSubstitutedLiterals(final TTSubstitution sub) {
		assert false : "TODO reimplement";
		return null;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("{");
		String comma = "";

		for (final ClauseLiteral cl : getLiterals()) {
			sb.append(comma);
			sb.append(cl.toString());
			comma = ", ";
		}

		sb.append("}");
		return sb.toString();
	}

	public Set<Clause> getGroundings(final DawgState<ApplicationTerm, Boolean> groundingDawg) {
		if (mIsGround) {
			assert groundingDawg.isFinal();
			return groundingDawg.getFinalValue()
					? Collections.singleton(new Clause(mDpllLiterals.toArray(new Literal[mDpllLiterals.size()])))
					: Collections.emptySet();
		}

		final Set<Clause> result = new HashSet<>();

		for (final List<ApplicationTerm> point : DawgFactory.getSet(groundingDawg)) {
			final Set<Literal> groundLits = getGroundingForPoint(point).getDomain();

			result.add(new Clause(groundLits.toArray(new Literal[groundLits.size()])));
		}

		return result;
	}


	/**
	 * Obtains a grounding of the clause for one point.
	 * The point needs to be in the clause's signature.
	 * Also tracks which instantiation comes from which ClauseLiteral -- which is useful for observing if a factoring has occurred.
	 * @param point
	 * @return
	 */
	private BinaryRelation<Literal, ClauseLiteral> getGroundingForPoint(final List<ApplicationTerm> point) {
		final TTSubstitution sub = new TTSubstitution(mVariables, point);
		final Set<Literal> groundLits = new HashSet<>();
//		Map<ClauseEprQuantifiedLiteral, Literal> quantifiedLitToInstantiation
		final BinaryRelation<Literal, ClauseLiteral> instantiationToClauseLiteral =
				new BinaryRelation<>();
		for (final ClauseLiteral cl : getLiterals()) {
			if (cl instanceof ClauseEprQuantifiedLiteral) {
				final ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
				final Term[] ceqlArgs = ceql.mArgumentTerms.toArray(new Term[ceql.mArgumentTerms.size()]);
				final TermTuple newTT = sub.apply(new TermTuple(ceqlArgs));
				assert newTT.getFreeVars().size() == 0;
				final EprPredicateAtom at = ceql.getEprPredicate().getAtomForTermTuple(
						newTT,
						mEprTheory.getTheory(),
						mEprTheory.getClausifier().getStackLevel(),
						ceql.getAtom().getSourceAnnotation());

				final Literal newLit = cl.getPolarity() ? at : at.negate();

				instantiationToClauseLiteral.addPair(newLit, ceql);
				groundLits.add(newLit);
			} else {
				instantiationToClauseLiteral.addPair(cl.getLiteral(), cl);
				groundLits.add(cl.getLiteral());
			}
		}
		return instantiationToClauseLiteral;
	}


	/**
	 * Checks if in the current decide state a factoring of this conflict clause is possible.
	 * If a factoring is possible, a factored clause is returned.
	 * Otherwise this clause is returned unchanged.
	 *
	 * @return A factored version of this clause or this clause.
	 */
	public EprClause factorIfPossible() {
		// assert this.isConflict();

		for (final List<ApplicationTerm> cp : DawgFactory.getSet(getConflictPoints())) {
			final BinaryRelation<Literal, ClauseLiteral> cpg = getGroundingForPoint(cp);

			for (final Literal groundLit : cpg.getDomain()) {
				final Set<ClauseLiteral> preGroundingClauseLits = cpg.getImage(groundLit);
				if (preGroundingClauseLits.size() == 1) {
					// no factoring occurred for that literal
					continue;
				}
				assert preGroundingClauseLits.size() > 1;
				/*
				 *  factoring occurred for that literal
				 *  that literal is a conflict grounding of this conflict epr clause
				 *  --> we can factor this conflict epr clause
				 */
				assert preGroundingClauseLits.size() == 2 : "TODO: deal with factoring for more than two literals";
				ClauseEprQuantifiedLiteral ceql = null;
				ClauseEprLiteral cel = null;
				for (final ClauseLiteral cl : preGroundingClauseLits) {
					assert cl instanceof ClauseEprLiteral;
					if (ceql == null && cl instanceof ClauseEprQuantifiedLiteral) {
						ceql = (ClauseEprQuantifiedLiteral) cl;
					} else if (cel == null &&
							(ceql != null || !(cl instanceof ClauseEprQuantifiedLiteral))) {
						cel = (ClauseEprLiteral) cl;
					}
				}
				assert cel != null && ceql != null && !cel.equals(ceql);


				mEprTheory.getLogger().debug("EPRDEBUG: (EprClause): factoring " + this);
				final EprClause factor = mEprTheory.getEprClauseFactory().getFactoredClause(ceql, cel);
				assert factor.isConflict() : "we only factor conflicts -- we should get a conflict out, too.";
				return factor;
			}
		}

		// when we can't factor, we just return this clause
		return this;
	}
}
