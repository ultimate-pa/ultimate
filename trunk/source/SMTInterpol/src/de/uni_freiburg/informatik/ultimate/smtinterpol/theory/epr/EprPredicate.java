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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprGroundLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprQuantifiedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackDecisionLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackEntry;

/**
 * Represents an uninterpreted predicate that the EPR theory reasons about.
 * Stores and updates a model for that predicate.
 * If setting a literal leads to a conflict, that conflict is reported back to the DPLLEngine.
 *
 * @author Alexander Nutz
 */
public class EprPredicate {
	private final int mArity;
	private final FunctionSymbol mFunctionSymbol;

	/**
	 * Every predicate symbol has canonical TermVariables for each of its argument positions.
	 * They form the signature of the corresponding Dawgs on the decide stack.
	 */
	protected final SortedSet<TermVariable> mSignature;

	final EprTheory mEprTheory;

	/**
	 * Storage to track where this predicate occurs in the formula with at least one quantified argument.
	 */
	private final HashMap<EprClause, HashSet<ClauseEprLiteral>> mQuantifiedOccurences =
			new HashMap<>();

	private final HashMap<EprClause, HashSet<ClauseEprLiteral>> mGroundOccurences =
			new HashMap<>();

	private final HashSet<EprGroundPredicateAtom> mDPLLAtoms = new HashSet<>();

	private final HashMap<TermTuple, EprGroundPredicateAtom> mPointToAtom = new HashMap<>();
	private final HashMap<TermTuple, EprQuantifiedPredicateAtom> mTermTupleToAtom = new HashMap<>();

	private DawgState<ApplicationTerm, EprTheory.TriBool> mCurrentDecision;

	public EprPredicate(final FunctionSymbol fs, final EprTheory eprTheory) {
		mFunctionSymbol = fs;
		mArity = fs.getParameterSorts().length;
		mEprTheory = eprTheory;

		final TreeSet<TermVariable> tva = new TreeSet<>(EprHelpers.getColumnNamesComparator());
		for (int i = 0; i < mArity; i++) {
			final String tvName = mFunctionSymbol.getName() + "_" + i;
			tva.add(
					mEprTheory.getTheory().createFreshTermVariable(tvName, fs.getParameterSorts()[i]));

		}
		mSignature = tva;
		mCurrentDecision = mEprTheory.getDawgFactory().createConstantDawg(mSignature, EprTheory.TriBool.UNKNOWN);
	}

	public void addQuantifiedOccurence(final ClauseEprQuantifiedLiteral l, final EprClause eprClause) {
		HashSet<ClauseEprLiteral> val = mQuantifiedOccurences.get(eprClause);
		if (val == null) {
			val = new HashSet<>();
			mQuantifiedOccurences.put(eprClause, val);
		}
		val.add(l);
	}

	private HashMap<EprClause, HashSet<ClauseEprLiteral>> getQuantifiedOccurences() {
		return mQuantifiedOccurences;
	}

	public EprTheory getEprTheory() {
		return mEprTheory;
	}

	public DawgState<ApplicationTerm, EprTheory.TriBool> getDawg() {
		return mCurrentDecision;
	}

	public SortedSet<TermVariable> getSignature() {
		return mSignature;
	}

	public void setDawg(final DawgState<ApplicationTerm, EprTheory.TriBool> decision) {
		mCurrentDecision = decision;
	}

	public void addGroundOccurence(final ClauseEprGroundLiteral l, final EprClause eprClause) {
		HashSet<ClauseEprLiteral> val = mGroundOccurences.get(eprClause);
		if (val == null) {
			val = new HashSet<>();
			mGroundOccurences.put(eprClause, val);
		}
		val.add(l);
	}

	private HashMap<EprClause, HashSet<ClauseEprLiteral>> getGroundOccurences() {
		return mGroundOccurences;
	}

	public HashMap<EprClause, HashSet<ClauseEprLiteral>> getAllEprClauseOccurences() {
		final HashMap<EprClause, HashSet<ClauseEprLiteral>> quantifiedOccurences =
				getQuantifiedOccurences();
		final HashMap<EprClause, HashSet<ClauseEprLiteral>> groundOccurences =
				getGroundOccurences();

		final HashMap<EprClause, HashSet<ClauseEprLiteral>> allOccurences =
				new HashMap<>(quantifiedOccurences);
		for (final Entry<EprClause, HashSet<ClauseEprLiteral>> en : groundOccurences.entrySet()) {
			if (allOccurences.containsKey(en.getKey())) {
				allOccurences.get(en.getKey()).addAll(en.getValue());
			} else {
				allOccurences.put(en.getKey(), en.getValue());
			}
		}
		return allOccurences;
	}

	public void addDPLLAtom(final EprGroundPredicateAtom egpa) {
		mDPLLAtoms.add(egpa);
	}

	public HashSet<EprGroundPredicateAtom> getDPLLAtoms() {
		return mDPLLAtoms;
	}

	/**
	 * Retrieve the ground atom belonging to TermTuple tt.
	 * Creates a new atom if no atom exists for tt.
	 * Note: this method assumes that tt only contains constants.
	 * Use getAtomForTermTuple in order to obtain a quantified atom.
	 */
	private EprGroundPredicateAtom getAtomForPoint(final TermTuple point, final Theory mTheory,
			final int assertionStackLevel, final SourceAnnotation source) {
		assert point.getFreeVars().size() == 0 : "Use getAtomForTermTuple, if tt is quantified";
		EprGroundPredicateAtom result = mPointToAtom.get(point);
		if (result == null) {
			final ApplicationTerm newTerm = (ApplicationTerm) mTheory.term(mFunctionSymbol, point.terms);
			final int hash = newTerm.hashCode();
			if (this instanceof EprEqualityPredicate) {
				result = new EprGroundEqualityAtom(newTerm, hash,
					assertionStackLevel,
					(EprEqualityPredicate) this,
					source);
			} else {
				result = new EprGroundPredicateAtom(newTerm, hash,
					assertionStackLevel,
					this,
					source);
			}
			mPointToAtom.put(point, result);
			addDPLLAtom(result);
		}
		return result;
	}

	/**
	 * Retrieve the quantified atom belonging to TermTuple tt.
	 * Creates a new atom if no atom exists for tt.
	 * Note: this method assumes that tt has at least one TermVariable (i.e. is quantified).
	 * Use getAtomForPoint in order to obtain a ground atom.
	 * @param tt
	 * @param mTheory
	 * @param assertionStackLevel
	 * @param source
	 * @return
	 */
	private EprQuantifiedPredicateAtom getAtomForQuantifiedTermTuple(final TermTuple tt, final Theory mTheory,
			final int assertionStackLevel, final SourceAnnotation source) {
		assert tt.getFreeVars().size() > 0 : "Use getAtomForPoint, if tt is ground";
		EprQuantifiedPredicateAtom result = mTermTupleToAtom.get(tt);

		if (result == null) {
			final ApplicationTerm newTerm = (ApplicationTerm) mTheory.term(mFunctionSymbol, tt.terms);
			if (this instanceof EprEqualityPredicate) {
					result = new EprQuantifiedEqualityAtom(newTerm,
						0,
						assertionStackLevel,
						(EprEqualityPredicate) this,
						source);
			} else {
				result = new EprQuantifiedPredicateAtom(newTerm,
						0,
						assertionStackLevel,
						this,
						source);
			}
			mTermTupleToAtom.put(tt, result);
		}
		return result;
	}

	public EprPredicateAtom getAtomForTermTuple(final TermTuple tt, final Theory mTheory,
			final int assertionStackLevel, final SourceAnnotation source) {
		if (tt.getFreeVars().size() > 0) {
			return getAtomForQuantifiedTermTuple(tt, mTheory, assertionStackLevel, source);
		} else {
			return getAtomForPoint(tt, mTheory, assertionStackLevel, source);
		}
	}

	@Override
	public String toString() {

		final String res = "EprPred: " + mFunctionSymbol.getName();
		if (res.contains("AUX")) {
			return "EprPred: (AUX " + hashCode() + ")";
		}
		return res;
	}

	/**
	 *
	 *  @return null if the model of this predicate is already complete, a DecideStackLiteral
	 *          otherwise.
	 */
	public DecideStackEntry getNextDecision() {
		/*
		 * For equalities our default decision is polarity "false", otherwise "true"
		 */
		final EprTheory.TriBool newDecision = this instanceof EprEqualityPredicate ? EprTheory.TriBool.TRUE
				: EprTheory.TriBool.FALSE;
		final DawgState<ApplicationTerm, EprTheory.TriBool> undecidedPoints =
				mEprTheory.getDawgFactory().createMapped(getDawg(),
						val -> val == EprTheory.TriBool.UNKNOWN ? newDecision : EprTheory.TriBool.UNKNOWN);

		if (DawgFactory.isConstantValue(undecidedPoints, EprTheory.TriBool.UNKNOWN)) {
			// no undecided points
			return null;
		} else {
			return new DecideStackDecisionLiteral(this, undecidedPoints);
		}
	}

	/**
	 * Called when an EprClause is disposed of (typically because of a pop command).
	 * Updates internal data structures of this EprPredicate accordingly.
	 *
	 * @param eprClause
	 */
	public void notifyAboutClauseDisposal(final EprClause eprClause) {
		mQuantifiedOccurences.remove(eprClause);
		mGroundOccurences.remove(eprClause);
	}

	public int getArity() {
		return mArity;
	}

	public FunctionSymbol getFunctionSymbol() {
		return mFunctionSymbol;
	}

	public SortedSet<TermVariable> getTermVariablesForArguments() {
		return mSignature;
	}

	public Sort[] getSorts() {
		return mFunctionSymbol.getParameterSorts();
	}
}
