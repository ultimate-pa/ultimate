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

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EprHelpers {

	/**
	 * Goes through all the given literals
	 * and adds all appearing constants to mAppearingConstants
	 */
	public static HashSet<ApplicationTerm> collectAppearingConstants(final Literal[] literals, final Theory theory) {
		final HashSet<ApplicationTerm> result = new HashSet<>();
		for (final Literal l : literals) {
			final DPLLAtom atom = l.getAtom();
			final Term t = atom.getSMTFormula(theory);
			if (!(t instanceof ApplicationTerm)) {
				continue;
			}
			if (!(atom instanceof EprAtom || atom instanceof CCEquality)) {
				continue;
			}
			for (final Term p : ((ApplicationTerm) t).getParameters()) {
				if (p instanceof ApplicationTerm) {
					assert ((ApplicationTerm) p).getFunction().getParameterSorts().length == 0;
					result.add((ApplicationTerm) p);
				}
			}
		}
		return result;
	}

	public static Literal applySubstitution(final TTSubstitution sub, final Literal l, final EprTheory eprTheory) {
		return applySubstitution(sub, l, eprTheory, false);
	}
	/**
	 * Apply the substitution sub to Literal l, return the result
	 * @param sub
	 * @param l
	 * @param theory
	 * @param calledFromDER the DER-case is special if we are in completeGroundingMode
	 * @return
	 */
	public static Literal applySubstitution(final TTSubstitution sub, final Literal l, final EprTheory eprTheory, final boolean calledFromDER) {
		final boolean isPositive = l.getSign() == 1;
		final DPLLAtom atom = l.getAtom();

		final Theory theory = eprTheory.getTheory();

		Literal resultLit = null;
		DPLLAtom resultAtom = null;

		if (atom instanceof EprQuantifiedPredicateAtom) {
			final EprQuantifiedPredicateAtom eqpa = (EprQuantifiedPredicateAtom) atom;
			final TermTuple newTT = sub.apply(eqpa.getArgumentsAsTermTuple());

			resultAtom = eqpa.getEprPredicate().getAtomForTermTuple(newTT, theory,
					eprTheory.getClausifier().getStackLevel(), eqpa.getSourceAnnotation());
		} else if (atom instanceof EprQuantifiedEqualityAtom) {
			final EprQuantifiedEqualityAtom eea = (EprQuantifiedEqualityAtom) atom;
			final TermTuple newTT = sub.apply(eea.getArgumentsAsTermTuple());
			final ApplicationTerm newTerm = (ApplicationTerm) theory.term("=", newTT.terms);

			if (newTerm.getFreeVars().length > 0) {
				assert false : "TODO: reactivate below code?";
//				resultAtom = new EprQuantifiedEqualityAtom(newTerm,
//						0, //TODO: hash
//						l.getAtom().getAssertionStackLevel(),
//						eprTheory.getEqualityEprPredicate());
			} else {
				// TODO: will need a management for these atoms -- so there are no duplicates..
				//   it's not clear if we want CCEqualities or so, here..
				assert false : "TODO: reactivate below code?";
//				int assertionStackLevel = eprTheory.getClausifier().getStackLevel();
//				resultAtom =  new EprGroundEqualityAtom(newTerm, 0, assertionStackLevel);
			}
		} else {
			//assert false : "there might be equality replacements"; --> seems idiotic now..
			// literal is ground, just return it
			return l;
		}


		if (EprTheorySettings.FullInstatiationMode) {
			// we are in the mode where Epr just computes all the groundings of each
			// quantified formula
			// --> thus EprAtoms must become CCEqualities

			final SourceAnnotation source = ((EprAtom) resultAtom).getSourceAnnotation();

			final Clausifier clausif = eprTheory.getClausifier();
			if (resultAtom instanceof EprGroundPredicateAtom) {
				// basically copied from Clausifier.createBooleanLit()
				final Term t = ((EprGroundPredicateAtom) resultAtom).getTerm();

				final EqualityProxy eq = clausif.createEqualityProxy(t, eprTheory.getTheory().mTrue, source);
				// Safe since m_Term is neither true nor false
				assert eq != EqualityProxy.getTrueProxy();
				assert eq != EqualityProxy.getFalseProxy();
				resultAtom = eq.getLiteral(source);
			} else if (resultAtom instanceof EprGroundEqualityAtom) {
				final Term t1 = ((EprAtom) resultAtom).getArguments()[0];
				final Term t2 = ((EprAtom) resultAtom).getArguments()[1];
				if (t1.equals(t2)) {
					resultAtom = new DPLLAtom.TrueAtom();
				} else {
					final EqualityProxy eq = clausif.createEqualityProxy(t1, t2, source);
					resultAtom = eq.getLiteral(source);
				}
			} else {
				assert calledFromDER : "not called from DER, but not ground, as it looks"
						+ " -- should not happen, right??";
			}
		}
		resultLit =  isPositive ? resultAtom : resultAtom.negate();
		return resultLit;
	}

	/**
	 * sub is a unifier for the predicateAtoms in setEqlwe and clauseLit.
	 * Apply sub to the equalities in setEqlwe and eprEqualityAtoms,
	 * return the result as a clause.
	 * @param setEqlwe
	 * @param clauseLit
	 * @param eprEqualityAtoms
	 * @param sub
	 * @return
	 */
	public static Literal[] applyUnifierToEqualities(final EprQuantifiedEqualityAtom[] eprEqualityAtoms1,
			final EprQuantifiedEqualityAtom[] eprEqualityAtoms2, final TTSubstitution sub, final EprTheory eprTheory) {

		final ArrayList<Literal> result = new ArrayList<>();
		for (final EprQuantifiedEqualityAtom eea : eprEqualityAtoms1) {
			result.add(EprHelpers.applySubstitution(sub, eea, eprTheory));
		}
		for (final EprQuantifiedEqualityAtom eea : eprEqualityAtoms2) {
			result.add(EprHelpers.applySubstitution(sub, eea, eprTheory));
		}

		return result.toArray(new Literal[result.size()]);
	}

	public static ArrayList<DPLLAtom> substituteInExceptions(
			final EprQuantifiedEqualityAtom[] equalities, final TTSubstitution sub, final EprTheory eprTheory) {

		final ArrayList<DPLLAtom> result = new ArrayList<>();
		for (final EprQuantifiedEqualityAtom eea : equalities) {
			result.add((DPLLAtom) EprHelpers.applySubstitution(sub, eea, eprTheory));
		}
		return result;
	}

//	public static class Pair<T,U> {
//		public final T first;
//		public final U second;
//
//		public Pair(T f, U s) {
//			first = f;
//			second = s;
//		}
//	}

	/**
	 * When we are sure (or want to be sure) that a Term array really only contains constants,
	 * we make the cast using this method.
	 * @param arguments
	 * @return
	 */
	public static ApplicationTerm[] castTermsToConstants(final Term[] arguments) {
		final ApplicationTerm[] ats = new ApplicationTerm[arguments.length];
		for (int i = 0; i < arguments.length; i++) {
			assert arguments[i] instanceof ApplicationTerm &&
			   ((ApplicationTerm) arguments[i]).getParameters().length == 0
			   : "This method should only be called on arrays of constants";
			ats[i] = (ApplicationTerm) arguments[i];
		}
		return ats;
	}

	/**
	 * Given a set S, computes S x S ... x S = S^n
	 */
	public static <LETTER> Set<List<LETTER>> computeNCrossproduct(final Set<LETTER> baseSet, final int n, final LogProxy logger) {
//		logger.debug("EPRDEBUG: EprHelpers.computeNCrossproduct N = " + n + " baseSet size = " + baseSet.size());
		Set<List<LETTER>> result = new HashSet<>();
		result.add(new ArrayList<LETTER>());
		for (int i = 0; i < n; i++) {
			final Set<List<LETTER>> newResult = new HashSet<>();
			for (final List<LETTER> tuple : result) {
				for (final LETTER ltr : baseSet) {
					final List<LETTER> newTuple = new ArrayList<>(tuple);
					newTuple.add(ltr);
					newResult.add(newTuple);
				}
			}
			result = newResult;
		}
		return result;
	}

//	public class EprClauseIterable implements Iterable<EprClause> {
//
//		Iterator<EprPushState> mPushStateStack;
//
//		public EprClauseIterable(Stack<EprPushState> pushStateStack) {
//			mPushStateStack = pushStateStack.iterator();
//		}
//
//		@Override
//		public Iterator<EprClause> iterator() {
//			return new EprClauseIterator();
//		}
//
//		class EprClauseIterator implements Iterator<EprClause> {
//			EprClause mNext;
//			Iterator<EprClause> mCurrentPushStateClauseIterator;
//
//			EprClauseIterator() {
//				mNext = findNextEprClause();
//			}
//
//			public EprClause findNextEprClause() {
//				if (! mPushStateStack.hasNext()) {
//					return null;
//				}
//				mCurrentPushStateClauseIterator = mPushStateStack.next().getClausesIterator();
//
//				// look for the first push state that has a clause
//				while (! mCurrentPushStateClauseIterator.hasNext()) {
//					if (!mPushStateStack.hasNext()) {
//						return null;
//					}
//					mCurrentPushStateClauseIterator = mPushStateStack.next().getClausesIterator();
//				}
//				return mCurrentPushStateClauseIterator.next();
//			}
//
//			@Override
//			public boolean hasNext() {
//				return mNext != null;
//			}
//
//			@Override
//			public EprClause next() {
//				mNext = findNextEprClause();
//				return mNext;
//			}
//		}
//	}
//
//	public class DecideStackLiteralIterable implements Iterable<DecideStackLiteral> {
//
//		Iterator<EprPushState> mPushStateStack;
//
//		public DecideStackLiteralIterable(Stack<EprPushState> pushStateStack) {
//			mPushStateStack = pushStateStack.iterator();
//		}
//
//		@Override
//		public Iterator<DecideStackLiteral> iterator() {
//			return new DSLIterator();
//		}
//
//		class DSLIterator implements Iterator<DecideStackLiteral> {
//			DecideStackLiteral mNext;
//			Iterator<DecideStackLiteral> mCurrentPushStateClauseIterator;
//
//			DSLIterator() {
//				mNext = findNextEprClause();
//			}
//
//			public DecideStackLiteral findNextEprClause() {
//				if (! mPushStateStack.hasNext()) {
//					return null;
//				}
//				mCurrentPushStateClauseIterator = mPushStateStack.next().getDecideStackLiteralIterator();
//
//				// look for the first push state that has a clause
//				while (! mCurrentPushStateClauseIterator.hasNext()) {
//					if (!mPushStateStack.hasNext()) {
//						return null;
//					}
//					mCurrentPushStateClauseIterator = mPushStateStack.next().getDecideStackLiteralIterator();
//				}
//				return mCurrentPushStateClauseIterator.next();
//			}
//
//			@Override
//			public boolean hasNext() {
//				return mNext != null;
//			}
//
//			@Override
//			public DecideStackLiteral next() {
//				mNext = findNextEprClause();
//				return mNext;
//			}
//		}
//	}

	public static <COLNAMES> COLNAMES[] applyMapping(
			final COLNAMES[] colnames, final Map<COLNAMES, COLNAMES> translation) {
		assert colnames.length > 0;
		final COLNAMES[] result = colnames.clone();
		for (int i = 0; i < colnames.length; i++) {
			final COLNAMES newEntry = translation.get(colnames[i]);
			if (newEntry != null) {
				result[i] = newEntry;
			}
		}
		return result;
	}

	public static <COLNAMES> List<COLNAMES> applyMapping(
			final List<COLNAMES> colnames, final Map<COLNAMES, COLNAMES> translation) {
		assert colnames.size() > 0;
		final List<COLNAMES> result = new ArrayList<>();
		for (final COLNAMES cn : colnames) {
			final COLNAMES newEntry = translation.get(cn);
			if (newEntry != null) {
				result.add(newEntry);
			} else {
				result.add(cn);
			}
		}
		return result;
	}

	public static <COLNAMES> SortedSet<COLNAMES> applyMapping(
			final SortedSet<COLNAMES> colnames, final Map<COLNAMES, COLNAMES> translation) {
		assert colnames.size() > 0;
		final SortedSet<COLNAMES> result = new TreeSet<>(EprHelpers.getColumnNamesComparator());
		for (final COLNAMES cn : colnames) {
			final COLNAMES newEntry = translation.get(cn);
			if (newEntry != null) {
				result.add(newEntry);
			} else {
				result.add(cn);
			}
		}
		return result;
	}
	public static List<ApplicationTerm> convertTermListToConstantList(final List<Term> constants) {
	    final List<ApplicationTerm> result = new ArrayList<>(constants.size());
		for (final Term t : constants) {
			result.add((ApplicationTerm) t);
		}
		return result;
	}

	public static List<ApplicationTerm> convertTermArrayToConstantList(final Term[] constants) {
	    final List<ApplicationTerm> result = new ArrayList<>(constants.length);
		for (int i = 0; i < constants.length; i++) {
			result.add((ApplicationTerm) constants[i]);
		}
		return result;
	}

	/**
	 * Provides a Comparator for the SortedSets we use for the dawg signatures.
	 * TODO: we really only need one instance of this.. (but what was the best way to have a singleton again?..)
	 * @return
	 */
	public static <COLNAMES> Comparator<COLNAMES> getColumnNamesComparator() {
		return ColNameComparator.getInstance();
	}

	static class ColNameComparator<COLNAMES> implements Comparator<COLNAMES> {

		private static ColNameComparator instance = new ColNameComparator();

		private ColNameComparator() {
		}

		@SuppressWarnings("unchecked")
		public static <COLNAMES> ColNameComparator<COLNAMES> getInstance() {
			return instance;
		}

		@Override
		public int compare(final COLNAMES o1, final COLNAMES o2) {
			// we can only deal with TermVariables and Strings right now --> otherwise this will throw an exception...
			if (o1 instanceof TermVariable) {
				final TermVariable tv1 = (TermVariable) o1;
				final TermVariable tv2 = (TermVariable) o2;
				return tv1.getName().compareTo(tv2.getName());
			} else if (o1 instanceof String) {
				return ((String) o1).compareTo((String) o2);
			} else if (o1 instanceof Integer) {
				return ((Integer) o1).compareTo((Integer) o2);
			}

			throw new UnsupportedOperationException("unexpected comparator call");
//			return o1.toString().compareTo(o2.toString());//might work for all..
		}

	}

	public static <COLNAMES> Map<COLNAMES, Integer> computeColnamesToIndex(final SortedSet<COLNAMES> sortedSet) {
		final Map<COLNAMES, Integer> result = new HashMap<>();

		final Iterator<COLNAMES> sortedSetIt = sortedSet.iterator();
		for (int i = 0; i < sortedSet.size(); i++) {
			final COLNAMES ithElement = sortedSetIt.next();
			result.put(ithElement, i);
		}
		return result;
	}
	/**
	 * Computes all the instantiations of the variables in freeVars that
	 * are added to the set of instantiations of oldConstants by adding one
	 * or more constants from newConstants.
	 * In other words: compute all instantiations of freeVars where a new constant occurs
	 * at least once.
	 *
	 * @param freeVars
	 * @param newConstant
	 * @param oldConstants
	 * @return
	 */
	public static ArrayList<TTSubstitution> getAllInstantiationsForNewConstant(
			final Set<TermVariable> freeVars,
			final Set<ApplicationTerm> newConstants,
			final Set<ApplicationTerm> oldConstants) {

		ArrayList<TTSubstitution> instsWithNewConstant =
				new ArrayList<>();
		ArrayList<TTSubstitution> instsWithOutNewConstant =
				new ArrayList<>();

		final HashSet<ApplicationTerm> allConstants = new HashSet<>(oldConstants);
		allConstants.addAll(newConstants);

		instsWithNewConstant.add(new TTSubstitution());
		instsWithOutNewConstant.add(new TTSubstitution());

		for (final TermVariable tv : freeVars) {
			final ArrayList<TTSubstitution> instsNewWNC = new ArrayList<>();
			final ArrayList<TTSubstitution> instsNewWONC = new ArrayList<>();
			for (final TTSubstitution sub : instsWithNewConstant) {
				for (final ApplicationTerm con : allConstants) {
					if (con.getSort().getRealSort() == tv.getSort().getRealSort()) {
						final TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNewWNC.add(newSub);
					}
				}
			}

			for (final TTSubstitution sub : instsWithOutNewConstant) {
				for (final ApplicationTerm con : oldConstants) {
					if (con.getSort().equals(tv.getSort())) {
						final TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNewWONC.add(newSub);
					}
				}
				for (final ApplicationTerm newConstant : newConstants) {
					if (newConstant.getSort().equals(tv.getSort())) {
						final TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(newConstant, tv);
						instsNewWNC.add(newSub);
					}
				}
			}
			instsWithNewConstant = instsNewWNC;
			instsWithOutNewConstant = instsNewWONC;
		}
		return instsWithNewConstant;
	}

	public static ArrayList<TTSubstitution> getAllInstantiations(
			final Set<TermVariable> freeVars,
			final Set<ApplicationTerm> constants) {
		ArrayList<TTSubstitution> insts = new ArrayList<>();
		insts.add(new TTSubstitution());

		for (final TermVariable tv : freeVars) {
			final ArrayList<TTSubstitution> instsNew = new ArrayList<>();
			for (final TTSubstitution sub : insts) {
				for (final ApplicationTerm con : constants) {
					if (con.getSort().getRealSort() == tv.getSort().getRealSort()) {
						final TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNew.add(newSub);
					}
				}
			}
			insts = instsNew;
		}
		return insts;
	}


	/**
	 * Checks if the sort of the entries of the points match the sort of their columns
	 * @param point
	 * @param colnames
	 * @return
	 */
	public static <LETTER, COLNAMES> boolean verifySortsOfPoints(final Iterable<List<LETTER>> points, final SortedSet<COLNAMES> colnames) {
		return true;
//		short i = 0;
//		for (List<LETTER> point : points) {
//			if (++i == 1000) {
//				System.err.print(".");
//				System.err.flush();
//				i = 0;
//			}
//
//			if (!verifySortsOfPoint(point, colnames)) {
//				return false;
//			}
//		}
//		return true;
	}

	/**
	 * Checks if the sort of the entries of the point match the sort of their columns
	 * @param point
	 * @param colnames
	 * @return
	 */
	public static <LETTER, COLNAMES> boolean verifySortsOfPoint(final List<LETTER> point, final SortedSet<COLNAMES> colnames) {
		if (point.size() == 0) {
			return true;
		}
		if (!(point.get(0) instanceof ApplicationTerm)
				|| !(colnames.iterator().next() instanceof TermVariable)) {
			// this method only applies if Colnames is TermVariable and Letter is ApplicationTerm
			return true;
		}
		final Iterator<COLNAMES> colnamesIt = colnames.iterator();
		for (int i = 0; i< point.size(); i++) {
			final ApplicationTerm pointAtI = (ApplicationTerm) point.get(i);
			final TermVariable colnameTvI = (TermVariable) colnamesIt.next();

			if (pointAtI.getSort().getRealSort() != colnameTvI.getSort().getRealSort()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Checks if, given the contained literal's decide statuses, if the given
	 * clause is currently a unit claus with the given literal as unit literal.
	 * This is the variant where we expect that the unit literal is (still) fulfilled.
	 * @param reason
	 * @param l
	 * @return
	 */
	public static boolean verifyUnitClauseAfterPropagation(final Clause reason, final Literal l, final LogProxy logger) {
		return verifyUnitClause(reason, l, true, null, logger);
	}

	/**
	 * Checks if, given the contained literal's decide statuses, if the given
	 * clause is currently a unit claus with the given literal as unit literal.
	 * This is the variant where we expect that the unit literal is (still) undecided.
	 */
	public static boolean verifyUnitClauseBeforePropagation(final Clause reason, final Literal l, final LogProxy logger) {
		return verifyUnitClause(reason, l, false, null, logger);
	}

	private static boolean verifyUnitClause(final Clause reason, final Literal l, final boolean afterPropagation,
			final Deque<Literal> literalsWaitingToBePropagated, final LogProxy logger) {
		for (int i = 0; i < reason.getSize(); i++) {
			final Literal curLit = reason.getLiteral(i);
			if (curLit == l) {
				if (afterPropagation && curLit.getAtom().getDecideStatus() != curLit) {
					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): The unit literal " + l + " is not set.");
					return false;
				} else if  (!afterPropagation && curLit.getAtom().getDecideStatus() != null) {
					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): The unit literal " + l + " is not undecided.");
					return false;
				}
			} else {
				//curLit != l

				final boolean refutedInDPLLEngine = curLit.getAtom().getDecideStatus() == curLit.negate();
				final boolean refutationQueuedForPropagation = literalsWaitingToBePropagated != null
						&& literalsWaitingToBePropagated.contains(curLit.negate());

				if (!refutedInDPLLEngine && !refutationQueuedForPropagation) {
					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): Literal " + curLit +
							" is not the unit literal but is not currently refuted");
					return false;
				}
			}
		}
		return true;
	}

	public static boolean verifyConflictClause(final Clause conflict, final LogProxy logger) {
		if (conflict == null) {
			return true;
		}
		for (int i = 0; i < conflict.getSize(); i++) {
			final Literal curLit = conflict.getLiteral(i);
			assert !(curLit.getAtom() instanceof EprGroundEqualityAtom) : "TODO: deal with this case";
			if (curLit.getAtom().getDecideStatus() != curLit.negate()) {
				logger.error("EPRDEBUG: (EprHelpers.verifyConflictClause): Literal " + curLit +
						" is not currently refuted");
				return false;
			}
		}
		return true;
	}

	public static boolean verifyUnitClauseAtEnqueue(final Literal l, final Clause reason,
			final Deque<Literal> mLiteralsWaitingToBePropagated, final LogProxy logger) {
//		for (int i = 0; i < reason.getSize(); i++) {
//			Literal curLit = reason.getLiteral(i);
//
//			if (curLit == l) {
//				if (afterPropagation && curLit.getAtom().getDecideStatus() != curLit) {
//					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): The unit literal " + l + " is not set.");
//					return false;
//				} else if  (!afterPropagation && curLit.getAtom().getDecideStatus() != null) {
//					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): The unit literal " + l + " is not undecided.");
//					return false;
//				}
//			}
//			if (curLit != l && curLit.getAtom().getDecideStatus() != curLit.negate()) {
//				logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): Literal " + curLit +
//						" is not the unit literal but is not currently refuted");
//				return false;
//			}
//
//		}

		return verifyUnitClause(reason, l, false, mLiteralsWaitingToBePropagated, logger);
	}

	/**
	 * Transforms a signature according to the given translation.
	 * <p>
	 * The translation is a map from  column names in the old signature to sets of column names in the new signature.
	 * If a column name in the old signature is not mentioned in the translation, it is left unchanged (thus will
	 * occur in the new signature).
	 * If an "old" column name is mapped to more than one column name, the "old" column name is removed and the new ones
	 * are added to the new signature.
	 *
	 * @param colNames
	 * @param renaming
	 * @return
	 */
	public static <COLNAMES> SortedSet<COLNAMES> transformSignature(final SortedSet<COLNAMES> colNames,
			final BinaryRelation<COLNAMES, COLNAMES> renaming) {
		final SortedSet<COLNAMES> result = new TreeSet<>(EprHelpers.getColumnNamesComparator());
		for (final COLNAMES oldCol : colNames) {
			final Set<COLNAMES> newCols = renaming.getImage(oldCol);
			if (newCols == null) {
				result.add(oldCol);
			}
			for (final COLNAMES newCol : newCols) {
				result.add(newCol);
			}
		}
		return result;
	}

	/**
	 * right now we only have different sorts when our colnames are of type TermVariable,
	 * otherwise we just have one dummy-String as Sort-Identifier.
	 */
	public static <COLNAMES> Object extractSortFromColname(final COLNAMES cn) {
		if (TermVariable.class.isInstance(cn)) {
			final TermVariable at = (TermVariable) cn;
			return at.getSort();
		}
//		assert false : "what to do here? (should only happen in unit-tests, right?)";
		return getDummySortId();
	}


	public static Object getDummySortId() {
		return "dummySort";
	}

	/**
	 * A ground conflict clause may need some sanitizing before it can be given to the DPLLEngine.
	 * This method does:
	 *  - eliminate EprGroundEqualityAtoms -- and replace them by CCEqualities
	 *  - some sanity checks
	 *
	 * @param conflict
	 * @param logger
	 * @return
	 */
	public static Clause sanitizeGroundConflict(final Clausifier clausif, final LogProxy logger, final Clause conflict) {
		final Clause result = replaceEprGroundEqualityAtoms(clausif, conflict);
		assert EprHelpers.verifyConflictClause(result, logger);
		return result;
	}

	public static Clause sanitizeReasonUnitClauseBeforeEnqueue(final Clausifier clausif, final LogProxy logger,
			final Literal l, final Clause reason, final Deque<Literal> literalsWaitingToBePropagated) {
		final Clause result = replaceEprGroundEqualityAtoms(clausif, reason);
		assert EprHelpers.verifyUnitClauseAtEnqueue(l, result, literalsWaitingToBePropagated, logger);
		return result;
	}

	private static Clause replaceEprGroundEqualityAtoms(final Clausifier clausif, final Clause conflict) {
		if (conflict == null) {
			return null;
		}
//		final Literal[] newLits = new Literal[conflict.getSize()];
		final List<Literal> newLits = new ArrayList<>(conflict.getSize());
		for (int i = 0; i < conflict.getSize(); i++) {
			final Literal lit = conflict.getLiteral(i);

			if (lit.getAtom() instanceof EprGroundEqualityAtom) {
				// EprGroundEqualityAtoms are a special case
				final EprGroundEqualityAtom egea = (EprGroundEqualityAtom) lit.getAtom();
				if (egea.getArguments()[0] == egea.getArguments()[1] && lit.getSign() != 1) {
					// the literal is equivalent to false -- just omit it
				} else if (egea.getArguments()[0] == egea.getArguments()[1] && lit.getSign() == 1) {
					assert false : "the given clause is equivalent to true; does this make sense??";
				} else {
					final CCEquality cceq = ((EprGroundEqualityAtom) lit.getAtom()).getCCEquality(clausif);
//					newLits[i] = lit.getSign() == 1 ? cceq : cceq.negate();
					newLits.add(lit.getSign() == 1 ? cceq : cceq.negate());
				}
			} else {
				// leave the literal as is
//				newLits[i] = lit;
				newLits.add(lit);
			}
		}
		final Clause result = new Clause(newLits.toArray(new Literal[newLits.size()]));
		return result;
	}

	public static boolean containsBooleanTerm(final Term[] parameters) {
		for (final Term t : parameters) {
			if ("Bool".equals(t.getSort().getRealSort().getName())) {
				return true;
			}
		}
		return false;
	}

}
