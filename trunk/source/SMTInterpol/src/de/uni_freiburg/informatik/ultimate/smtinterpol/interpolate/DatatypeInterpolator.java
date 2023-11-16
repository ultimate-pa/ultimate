/*
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for the Theory of datatypes.
 *
 * @author Leon Cacace, Jochen Hoenicke
 */
public class DatatypeInterpolator {

	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	// the equalities of the lemma
	private HashMap<SymmetricPair<Term>, LitInfo> mEqualityInfos;
	// the disequality of the lemma
	private HashMap<SymmetricPair<Term>, LitInfo> mDisequalityInfos;

	public DatatypeInterpolator(final Interpolator interpolator) {
		mInterpolator = interpolator;
		mTheory = interpolator.mTheory;
		mNumInterpolants = interpolator.mNumInterpolants;
	}

	/**
	 * Computes interpolants for a datatype lemma.
	 *
	 * @param clauseInfo the clause info for the datatype lemma.
	 * @return the array of interpolants
	 */
	public Term[] computeDatatypeInterpolants(final InterpolatorClauseInfo clauseInfo) {
		mEqualityInfos = new HashMap<>();
		mDisequalityInfos = new HashMap<>();
		for (final Term literal : clauseInfo.getLiterals()) {
			final ApplicationTerm atom = (ApplicationTerm) mInterpolator.getAtom(literal);
			final LitInfo atomOccurenceInfo = mInterpolator.getAtomOccurenceInfo(atom);
			final Term left = atom.getParameters()[0];
			final Term right = atom.getParameters()[1];
			final SymmetricPair<Term> pair = new SymmetricPair<>(left, right);
			if (atom != literal) {
				mEqualityInfos.put(pair, atomOccurenceInfo);
			} else {
				mDisequalityInfos.put(pair, atomOccurenceInfo);
			}
		}
		final Object[] annot = ((Object[]) clauseInfo.getLemmaAnnotation());

		switch (clauseInfo.getLemmaType()) {
		case ":dt-project":
			return interpolateDTProject(annot);
		case ":dt-tester":
			return interpolateDTTester(annot);
		case ":dt-constructor":
			return interpolateDTConstructor(annot);
		case ":dt-injective":
			return interpolateDTInjective(annot);
		case ":dt-disjoint":
			return interpolateDTDisjoint(annot);
		case ":dt-unique":
			return interpolateDTUnique(annot);
		case ":dt-cases":
			return interpolateDTCases(annot);
		case ":dt-cycle":
			return interpolateDTCycle(annot);
		default:
			throw new UnsupportedOperationException("lemma unknown in datatype interpolator");
		}
	}

	/**
	 * Interpolate a datatype uniqueness conflict. The conflict has the form
	 * {@code ((_ is cons1) u1) == true, ((_ is cons2) u2) == true, u1 == u2}. The
	 * last equality is missing if it is trivial.
	 *
	 * @param testers the argument of the :dt-unique annotation. It is a list of the
	 *                two tester terms {@code ((_ is consi) ui)}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTUnique(Object[] testers) {
		final ApplicationTerm firstTester = (ApplicationTerm) testers[0];
		final Term firstSymbol = firstTester.getParameters()[0];
		final LitInfo firstTesterInfo = mEqualityInfos.get(new SymmetricPair<>(mTheory.mTrue, firstTester));
		final ApplicationTerm secondTester = (ApplicationTerm) testers[1];
		final Term secondSymbol = secondTester.getParameters()[0];
		final LitInfo secondTesterInfo = mEqualityInfos.get(new SymmetricPair<>(mTheory.mTrue, secondTester));
		final LitInfo equalityInfo = (firstSymbol == secondSymbol) ? null
				: mEqualityInfos.get(new SymmetricPair<>(firstSymbol, secondSymbol));

		final Term[] interpolants = new Term[mNumInterpolants];
		for (int partition = 0; partition < mNumInterpolants; partition++) {
			Term interpolant;
			if (firstTesterInfo.isAorShared(partition) && secondTesterInfo.isAorShared(partition)) {
				// Both testers are in A
				if (equalityInfo != null && equalityInfo.isBLocal(partition)) {
					// equalityInfo is B local - interpolant is negated equality.
					interpolant = mTheory.term(SMTLIBConstants.NOT,
							mTheory.term(SMTLIBConstants.EQUALS, firstSymbol, secondSymbol));
				} else {
					// everything is in A
					interpolant = mTheory.mFalse;
				}
			} else if (firstTesterInfo.isBorShared(partition) && secondTesterInfo.isBorShared(partition)) {
				// both testers are in B
				if (equalityInfo != null && equalityInfo.isALocal(partition)) {
					// equality is in A, so that is the interpolant.
					interpolant = mTheory.term(SMTLIBConstants.EQUALS, firstSymbol, secondSymbol);
				} else {
					// everything is in B
					interpolant = mTheory.mTrue;
				}
			} else {
				// one tester is A-local, the other is B-local
				final ApplicationTerm aTester = firstTesterInfo.isALocal(partition) ? firstTester : secondTester;
				if (equalityInfo == null || equalityInfo.isBorShared(partition)) {
					// equality is in B, the aTester is the interpolant
					interpolant = aTester;
				} else if (equalityInfo.isMixed(partition)) {
					// equality is mixed, apply aTester.getFunction() to mixed var
					interpolant = mTheory.term(aTester.getFunction(), equalityInfo.getMixedVar());
				} else {
					// equality is A local, apply aTester.getFunction() to shared variable in second
					// tester.
					final Term sharedSymbol = firstTesterInfo.isALocal(partition) ? secondSymbol : firstSymbol;
					interpolant = mTheory.term(aTester.getFunction(), sharedSymbol);
				}
			}
			interpolants[partition] = interpolant;
		}
		return interpolants;
	}

	/**
	 * Interpolate a datatype dt-disjoint conflict. The conflict has the form
	 * {@code (cons a1 ... an) == (cons' b1 ... bn')}, where cons and cons' are
	 * different constructors.
	 *
	 * @param annot the argument of the :dt-disjoint annotation. It has the form
	 *              {@code :cons (cons a1 ... an) (cons' b1 ... bn'))}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTDisjoint(Object[] annot) {
		final Term[] interpolants = new Term[mNumInterpolants];

		final SymmetricPair<Term> eqLit = mEqualityInfos.keySet().iterator().next();
		final LitInfo eqInfo = mEqualityInfos.get(eqLit);

		for (int partition = 0; partition < mNumInterpolants; partition++) {
			if (eqInfo.isAorShared(partition)) {
				interpolants[partition] = mTheory.mFalse;
			} else if (eqInfo.isBLocal(partition)) {
				interpolants[partition] = mTheory.mTrue;
			} else {
				assert eqInfo.isMixed(partition);
				final Occurrence lhsOcc = eqInfo.getLhsOccur();
				final Term aTerm = lhsOcc.isALocal(partition) ? eqLit.getFirst() : eqLit.getSecond();
				final FunctionSymbol aCons = ((ApplicationTerm) aTerm).getFunction();
				interpolants[partition] = mTheory.term(SMTLIBConstants.IS, new String[] { aCons.getName() }, null,
						eqInfo.getMixedVar());
			}
		}
		return interpolants;
	}

	/**
	 * Interpolate a datatype dt-injective conflict. The conflict has the form
	 * {@code (cons a1 ... an) == (cons b1 ... bn), ai != bi}.
	 *
	 * @param annot the argument of the :dt-injective annotation. It has the form
	 *              {@code ((= ai bi) :cons (cons a1 ... an) (cons b1 ... bn))}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTInjective(Object[] annot) {
		final Term[] interpolants = new Term[mNumInterpolants];

		final ApplicationTerm diseqAtom = (ApplicationTerm) annot[0];
		final Term[] diseqParams = diseqAtom.getParameters();
		assert mDisequalityInfos.size() == 1;
		final SymmetricPair<Term> diseqPair = mDisequalityInfos.keySet().iterator().next();
		final LitInfo diseqInfo = mDisequalityInfos.get(diseqPair);
		final ApplicationTerm firstConsTerm = (ApplicationTerm) annot[2];
		final ApplicationTerm secondConsTerm = (ApplicationTerm) annot[3];
		final LitInfo eqInfo = mEqualityInfos.get(new SymmetricPair<>(firstConsTerm, secondConsTerm));
		String selFunc = null;

		for (int partition = 0; partition < mNumInterpolants; partition++) {
			if (diseqInfo.isAorShared(partition) && eqInfo.isAorShared(partition)) {
				interpolants[partition] = mTheory.mFalse;
			} else if (diseqInfo.isBorShared(partition) && eqInfo.isBorShared(partition)) {
				interpolants[partition] = mTheory.mTrue;
			} else if (diseqInfo.isALocal(partition) && eqInfo.isBLocal(partition)) {
				interpolants[partition] = mTheory.term(SMTLIBConstants.NOT, diseqAtom);
			} else if (diseqInfo.isBLocal(partition) && eqInfo.isALocal(partition)) {
				interpolants[partition] = diseqAtom;
			} else {
				assert eqInfo.isMixed(partition);
				if (selFunc == null) {
					selFunc = getSelectorForPair(firstConsTerm, secondConsTerm, diseqParams);
				}
				final Term sharedSelTerm = mTheory.term(selFunc, eqInfo.getMixedVar());
				if (diseqInfo.isAorShared(partition)) {
					final Term sharedTerm = eqInfo.getLhsOccur().isALocal(partition) ? diseqPair.getSecond()
							: diseqPair.getFirst();
					interpolants[partition] = mTheory.term(SMTLIBConstants.NOT,
							mTheory.term(SMTLIBConstants.EQUALS, sharedTerm, sharedSelTerm));
				} else if (diseqInfo.isBLocal(partition)) {
					final Term sharedTerm = eqInfo.getLhsOccur().isALocal(partition) ? diseqPair.getFirst()
							: diseqPair.getSecond();
					interpolants[partition] = mTheory.term(SMTLIBConstants.EQUALS, sharedTerm, sharedSelTerm);
				} else {
					interpolants[partition] = mTheory.term(Interpolator.EQ, diseqInfo.getMixedVar(), sharedSelTerm);
				}
			}
		}

		return interpolants;
	}

	/**
	 * Interpolate a datatype constructor conflict. The conflict has the form
	 * {@code is_cons(w) == true, w != cons(sel1(w),...,seln(w))}.
	 *
	 * @param annot the argument of the :dt-constructor annotation. It has the form
	 *              {@code (= w (cons (sel1 w) ... (seln w)))}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTConstructor(Object[] annot) {
		final Term[] interpolants = new Term[mNumInterpolants];

		final ApplicationTerm diseqAtom = (ApplicationTerm) annot[0];
		final Term[] diseqParams = diseqAtom.getParameters();
		final LitInfo diseqInfo = mDisequalityInfos.get(new SymmetricPair<>(diseqParams[0], diseqParams[1]));

		// tester
		final Term dataTerm = diseqParams[0];
		final FunctionSymbol constructor = ((ApplicationTerm) diseqParams[1]).getFunction();
		final ApplicationTerm testerTerm = (ApplicationTerm) mTheory.term(SMTLIBConstants.IS,
				new String[] { constructor.getName() }, null, dataTerm);
		final LitInfo testerInfo = mEqualityInfos.get(new SymmetricPair<Term>(testerTerm, mTheory.mTrue));

		for (int partition = 0; partition < mNumInterpolants; partition++) {
			if (testerInfo.isAorShared(partition) && diseqInfo.isAorShared(partition)) {
				interpolants[partition] = mTheory.mFalse;
			} else if (testerInfo.isBorShared(partition) && diseqInfo.isBorShared(partition)) {
				interpolants[partition] = mTheory.mTrue;
			} else if (testerInfo.isALocal(partition) && diseqInfo.isBLocal(partition)) {
				interpolants[partition] = testerTerm;
			} else if (testerInfo.isBLocal(partition) && diseqInfo.isALocal(partition)) {
				interpolants[partition] = mTheory.term(SMTLIBConstants.NOT, testerTerm);
			} else {
				// none of the equalities can be mixed.
				throw new AssertionError();
			}
		}

		return interpolants;
	}

	/**
	 * Interpolate a datatype tester conflict. The conflict has the form
	 * {@code w == cons(v1,...,vn), is_cons(w) != true} or
	 * {@code w == cons(v1,...,vn), is_cons'(w) != false}. The equality is missing
	 * if it is implied by reflexivity.
	 *
	 * @param annot the argument of the :dt-tester annotation. It has the form
	 *              {@code (= is_cons(w) true/false) :cons cons(v1,...,vn)}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTTester(Object[] annot) {

		final ApplicationTerm consTerm = (ApplicationTerm) annot[2];
		final ApplicationTerm goaleqTerm = (ApplicationTerm) annot[0];
		final Term testerArg = ((ApplicationTerm) goaleqTerm.getParameters()[0]).getParameters()[0];

		final SymmetricPair<Term> diseqLit = mDisequalityInfos.keySet().iterator().next();
		final LitInfo diseqInfo = mDisequalityInfos.get(diseqLit);

		final Term[] interpolants = new Term[mNumInterpolants];

		// equality is missing because it is trivial
		if (mEqualityInfos.size() == 0) {
			for (int partition = 0; partition < mNumInterpolants; partition++) {
				if (diseqInfo.isAorShared(partition)) {
					interpolants[partition] = mTheory.mFalse;
				} else {
					// can not be mixed as it is always (... != true/false)
					assert (diseqInfo.isBLocal(partition));
					interpolants[partition] = mTheory.mTrue;
				}
			}
			return interpolants;
		}
		assert (mEqualityInfos.size() == 1);

		final SymmetricPair<Term> eqLit = mEqualityInfos.keySet().iterator().next();
		final LitInfo eqInfo = mEqualityInfos.get(eqLit);


		for (int partition = 0; partition < mNumInterpolants; partition++) {
			if (diseqInfo.isAorShared(partition) && eqInfo.isAorShared(partition)) {
				interpolants[partition] = mTheory.mFalse;
			} else if (diseqInfo.isBorShared(partition) && eqInfo.isBorShared(partition)) {
				interpolants[partition] = mTheory.mTrue;
			} else {
				final Term sharedTerm = eqInfo.isMixed(partition) ? eqInfo.getMixedVar() : testerArg;
				if (diseqInfo.isALocal(partition)) {
					interpolants[partition] = mTheory.term("not", mTheory.term(SMTLIBConstants.IS,
							new String[] { consTerm.getFunction().getName() }, null, sharedTerm));
				} else {
					interpolants[partition] = mTheory.term(SMTLIBConstants.IS,
							new String[] { consTerm.getFunction().getName() }, null, sharedTerm);
				}
			}
		}
		return interpolants;
	}

	/**
	 * Interpolate a datatype project conflict. The conflict has the form
	 * {@code w == cons(v1,...,vn), seli(w) != vi}. The equality is missing if it is
	 * implied by reflexivity.
	 *
	 * @param annot the argument of the :dt-project annotation. It has the form
	 *              {@code (= seli(w) vi) :cons cons(v1,...,vn)}.
	 */
	private Term[] interpolateDTProject(Object[] annot) {

		final ApplicationTerm goalEq = (ApplicationTerm) annot[0];
		final Term[] interpolants = new Term[mNumInterpolants];

		// equality is missing because it is trivial
		if (mEqualityInfos.size() == 0) {
			final LitInfo diseqInfo = mDisequalityInfos.values().iterator().next();
			for (int partition = 0; partition < mNumInterpolants; partition++) {
				if (diseqInfo.isAorShared(partition)) {
					interpolants[partition] = mTheory.mFalse;
				} else if (diseqInfo.isBLocal(partition)) {
					interpolants[partition] = mTheory.mTrue;
				} else {
					// mixed case is possible only with quantifiers
					assert diseqInfo.isMixed(partition);
					final Term sharedTerm = goalEq.getParameters()[1];
					interpolants[partition] = mTheory.term(Interpolator.EQ, diseqInfo.getMixedVar(), sharedTerm);
				}
			}
			return interpolants;
		}
		assert (mEqualityInfos.size() == 1);
		if (mDisequalityInfos.size() == 0) {
			final LitInfo eqInfo = mDisequalityInfos.values().iterator().next();
			for (int partition = 0; partition < mNumInterpolants; partition++) {
				if (eqInfo.isAorShared(partition)) {
					interpolants[partition] = mTheory.mFalse;
				} else if (eqInfo.isBLocal(partition)) {
					interpolants[partition] = mTheory.mTrue;
				} else {
					throw new AssertionError();
				}
			}
			return interpolants;
		}
		assert (mDisequalityInfos.size() == 1);

		final SymmetricPair<Term> diseqLit = mDisequalityInfos.keySet().iterator().next();
		final LitInfo diseqInfo = mDisequalityInfos.get(diseqLit);

		final SymmetricPair<Term> eqLit = mEqualityInfos.keySet().iterator().next();
		final LitInfo eqInfo = mEqualityInfos.get(eqLit);

		for (int partition = 0; partition < mNumInterpolants; partition++) {
			if (eqInfo.isAorShared(partition) && diseqInfo.isAorShared(partition)) {
				interpolants[partition] = mTheory.mFalse;
			} else if (eqInfo.isBorShared(partition) && diseqInfo.isBorShared(partition)) {
				interpolants[partition] = mTheory.mTrue;
			} else {
				Term shared0Term, shared1Term;
				if (eqInfo.isMixed(partition)) {
					final Term consSharedTerm = eqInfo.getMixedVar();
					final ApplicationTerm selectTerm = (ApplicationTerm) goalEq.getParameters()[0];
					final FunctionSymbol selectSym = selectTerm.getFunction();
					shared0Term = shared1Term = mTheory.term(selectSym, consSharedTerm);
				} else {
					shared0Term = goalEq.getParameters()[0];
					shared1Term = goalEq.getParameters()[1];
				}
				if (diseqInfo.isMixed(partition)) {
					interpolants[partition] = mTheory.term(Interpolator.EQ, diseqInfo.getMixedVar(), shared1Term);
				} else if (diseqInfo.isALocal(partition)) {
					interpolants[partition] = mTheory.term(SMTLIBConstants.NOT,
							mTheory.term(SMTLIBConstants.EQUALS, shared0Term, goalEq.getParameters()[1]));
				} else {
					interpolants[partition] = mTheory.term(SMTLIBConstants.EQUALS, shared0Term,
							goalEq.getParameters()[1]);
				}
			}
		}
		return interpolants;
	}

	/**
	 * Interpolate a datatype cases conflict. The conflict has the form
	 * {@code ((_ is cons1) u1) == false, ... ((_ is consn) un) == false, u1 == u2,  ... u1 == un}.
	 * The u1 == uj equalities are missing if they are trivial.
	 *
	 * @param annot the argument of the :dt-cases annotation. It is a list of the
	 *              tester terms {@code ((_ is consi) ui)}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTCases(Object[] annot) {
		final Term[] interpolants = new Term[mNumInterpolants];

		final ApplicationTerm firstTerm = (ApplicationTerm) annot[0];
		final Term firstSymbol = firstTerm.getParameters()[0];
		final LitInfo firstTesterInfo = mEqualityInfos.get(new SymmetricPair<>(mTheory.mFalse, firstTerm));

		for (int partition = 0; partition < mNumInterpolants; partition++) {
			final boolean summarizeA = firstTesterInfo.isBorShared(partition);
			final ArrayList<Term> interpolantTerms = new ArrayList<>();
			for (int i = 1; i < annot.length; i++) {
				final Term term = (Term) annot[i];
				final Term symbol = ((ApplicationTerm) term).getParameters()[0];
				final LitInfo testerInfo = mEqualityInfos.get(new SymmetricPair<>(term, mTheory.mFalse));
				final LitInfo eqInfo = mEqualityInfos.get(new SymmetricPair<>(symbol, firstSymbol));
				final FunctionSymbol testerFunc = ((ApplicationTerm) term).getFunction();

				if (summarizeA ? testerInfo.isBorShared(partition) : testerInfo.isAorShared(partition)) {
					// only summarize the equality if it is the other partition
					assert eqInfo == null || !eqInfo.isMixed(partition);
					if (eqInfo != null && (summarizeA ? eqInfo.isALocal(partition) : eqInfo.isBLocal(partition))) {
						final Term eqTerm = mTheory.term(SMTLIBConstants.EQUALS, firstSymbol, symbol);
						interpolantTerms.add(summarizeA ? eqTerm : mTheory.term(SMTLIBConstants.NOT, eqTerm));
					}
				} else {
					// find shared term
					Term sharedTerm;
					if (eqInfo == null || (summarizeA ? eqInfo.isALocal(partition) : eqInfo.isBLocal(partition))) {
						sharedTerm = firstSymbol;
					} else if (eqInfo.isMixed(partition)) {
						sharedTerm = eqInfo.getMixedVar();
					} else {
						sharedTerm = symbol;
					}
					final Term testerTerm = mTheory.term(testerFunc, sharedTerm);
					interpolantTerms.add(summarizeA ? mTheory.term(SMTLIBConstants.NOT, testerTerm) : testerTerm);
				}
			}
			final Term[] components = interpolantTerms.toArray(new Term[interpolantTerms.size()]);
			if (summarizeA) {
				interpolants[partition] = mTheory.and(components);
			} else {
				interpolants[partition] = mTheory.or(components);
			}
		}
		return interpolants;
	}

	private String getSelectorForPair(ApplicationTerm cons1Term, ApplicationTerm cons2Term, Term[] childTerms) {
		final DataType datatype = (DataType) cons1Term.getSort().getSortSymbol();
		final Constructor cons = datatype.findConstructor(cons1Term.getFunction().getName());
		final String[] s = cons.getSelectors();
		final Term[] terms1 = cons1Term.getParameters();
		final Term[] terms2 = cons2Term.getParameters();
		for (int i = 0; i < terms1.length; i++) {
			if (childTerms[0] == terms1[i] && childTerms[1] == terms2[i]) {
				return s[i];
			}
		}
		throw new AssertionError("child term not found in constructors");
	}

	/**
	 * Interpolate a datatype dt-cycle conflict. The lemma is annotated with a cycle
	 * {@code a1,b1,a2,b2,..,an} that shows that {@code a1} is equal to a
	 * constructor call on itself. The conflict must contain {@code ai == bi} (if it
	 * is not trivial) and {@code a(i+1)} is a child of {@code bi} in the sense that
	 * either {@code bi} is a term {@code cons(..,a(i+1),...)}, or that
	 * {@code a(i+1)} is a term {@code sel(bi)} and for the corresponding
	 * constructor {@code is_cons(bi) = true} occurs negated in the lemma.
	 *
	 * @param annot the argument of the :dt-cycle annotation. It has the form
	 *              {@code :cycle a1 b1 a2 b2 ... an} where a1 == an.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTCycle(Object[] annot) {
		assert (annot[0] == ":cycle");
		final Term[] path = (Term[]) annot[1];
		assert mDisequalityInfos.isEmpty();
		return new DatatypeCycleInterpolator(mInterpolator, mEqualityInfos).interpolateCycle(path);
	}
}
