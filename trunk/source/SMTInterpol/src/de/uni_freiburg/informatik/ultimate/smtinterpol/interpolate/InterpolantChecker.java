/*
 * Copyright (C) 2009-2012 University of Freiburg
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

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;

public class InterpolantChecker {
	Interpolator mInterpolator;
	Script mCheckingSolver;
	Set<FunctionSymbol> mGlobals;

	public InterpolantChecker(final Interpolator interpolator, final Script checkingSolver) {
		mInterpolator = interpolator;
		mCheckingSolver = checkingSolver;
	}

	/**
	 * Fixup EQs by replacing any occurrence of EQ(x, s) with (let ((x s)) replacement).
	 *
	 * @param term
	 *            The term in which EQs should be replaced.
	 * @param fixupEQs
	 *            A map for EQ(x,s) from x to the replacement term, containing x as free variable. EQs whose variable is
	 *            not in this map remain unchanged.
	 * @param auxMaps
	 *            A map for x from x to a replacement term.
	 * @return The replaced term.
	 */
	private Term fixupAndLet(final Term interpolant, final HashMap<TermVariable, Term> fixedEQs,
			final HashMap<TermVariable, Term> auxMap) {
		final TermTransformer substitutor = new TermTransformer() {
			@Override
			public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
				final FunctionSymbol func = appTerm.getFunction();
				if (fixedEQs != null && func.isIntern() && func.getName().equals(Interpolator.EQ)) {
					final TermVariable tv = (TermVariable) appTerm.getParameters()[0];
					final Term replacement = fixedEQs.get(tv);
					if (replacement != null) {
						final Term sharedValue = newArgs[1];
						setResult(mInterpolator.substitute(replacement, tv, sharedValue));
						return;
					}
				}
				super.convertApplicationTerm(appTerm, newArgs);
			}

			@Override
			public void convert(Term term) {
				if (LAInterpolator.isLATerm(term)) {
					term = ((AnnotatedTerm) term).getSubterm();
				}
				if (auxMap != null && term instanceof TermVariable) {
					final Term replacement = auxMap.get(term);
					if (replacement != null) {
						setResult(replacement);
						return;
					}
				}
				super.convert(term);
			}
		};
		return substitutor.transform(interpolant);
	}

	/**
	 * Fix auxiliary variables by replacing them through constant terms. This is
	 * needed to obtain a closed formula.
	 *
	 * @param interpolant The term in which variables should be replaced.
	 * @param varToTerm   A map from auxiliary variables to their replacement term.
	 * @return The term with variables replaced by constant terms.
	 */
	private Term fixVars(Term interpolant, HashMap<TermVariable, Term> varToTerm) {
		for (final Term tv : interpolant.getFreeVars()) {
			final TermTransformer ipolator = mInterpolator.new TermSubstitutor(tv, varToTerm.get(tv));
				interpolant = ipolator.transform(interpolant);
		}
		return interpolant;
	}

	/**
	 * Purify a literal and directly fix the emerging purification variables by
	 * replacing them through constant terms. This is needed to obtain a closed
	 * formula.
	 *
	 * @param literal   The term that needs to be purified.
	 * @param varToTerm A map from auxiliary variables to their replacement term.
	 * @return The purified literal with purification variables replaced by constant
	 *         terms.
	 */
	private Term purifyAndFix(Term literal, HashMap<TermVariable, Term> varToTerm,
			HashMap<TermVariable, Term> varToFreshTerm) {
		for (final Entry<TermVariable, Term> e : varToFreshTerm.entrySet()) {
			final Term term = varToTerm.get(e.getKey());
			assert term != null;
			final TermTransformer ipolator = mInterpolator.new TermSubstitutor(term, e.getValue());
			literal = ipolator.transform(literal);
		}
		return literal;
	}

	public void checkInductivity(final Term[] literals, final Term[] ipls) {
		final LogProxy logger = mInterpolator.getLogger();
		final Theory theory = mInterpolator.mTheory;
		final int old = logger.getLoglevel();// NOPMD
		logger.setLoglevel(LogProxy.LOGLEVEL_ERROR);

		mCheckingSolver.push(1);

		/*
		 * initialize auxMaps, which maps for each partition the auxiliary variables for mixed literals to a new fresh
		 * constant.
		 */
		@SuppressWarnings("unchecked") // because Java Generics are broken :(
		final HashMap<TermVariable, Term>[] auxMaps = new HashMap[ipls.length];

		/*
		 * purVarToFreshTerm Get the mapping from all so far used purification variables
		 * to the terms they replaced.
		 */
		final HashMap<TermVariable, Term> purVarToTerm = mInterpolator.mPurifyDefinitions;
		final HashSet<TermVariable> activeVars = new HashSet<>();

		/*
		 * TODO: initialize purVarToFreshTerm, which maps the auxiliary variables used
		 * in the purified interpolant of at least one partition to a new fresh
		 * constant.
		 */
		final HashMap<TermVariable, Term> purVarToFreshTerm = new HashMap<>();
		for (final Entry<TermVariable, Term> e : purVarToTerm.entrySet()) {
			final TermVariable tv = e.getKey();
			if (!purVarToFreshTerm.containsKey(tv)) {
				final String name = ".check" + tv.getName();
				mCheckingSolver.declareFun(name, new Sort[0], tv.getSort());
				final Term constTerm = mCheckingSolver.term(name);
				purVarToFreshTerm.put(tv, constTerm);
			}
		}
		assert purVarToTerm.size() == purVarToFreshTerm.size();

		for (int i = 0; i < ipls.length; i++) {
			activeVars.addAll(Arrays.asList(ipls[i].getFreeVars()));
		}

		for (final Term lit : literals) {
			final Term atom = mInterpolator.getAtom(lit);
			final InterpolatorAtomInfo atomTermInfo = mInterpolator.getAtomTermInfo(atom);
			final LitInfo info = mInterpolator.getAtomOccurenceInfo(atom);
			final TermVariable tv = info.mMixedVar;
			if (tv != null) {
				Term auxTerm = null;
				for (int part = 0; part < ipls.length; part++) {
					if (info.isMixed(part)) {
						Term partAuxTerm;
						if (atomTermInfo.isCCEquality()) {
							// for CC all partitions shared the same aux variable.
							if (auxTerm == null) {
								final String name = ".check." + tv.getName();
								mCheckingSolver.declareFun(name, new Sort[0], tv.getSort());
								auxTerm = mCheckingSolver.term(name);
							}
							partAuxTerm = auxTerm;
						} else {
							// for LA every partition has its own aux variable as the A part changes
							final String name = ".check" + part + "." + tv.getName();
							mCheckingSolver.declareFun(name, new Sort[0], tv.getSort());
							partAuxTerm = mCheckingSolver.term(name);
						}
						if (auxMaps[part] == null) {
							auxMaps[part] = new HashMap<>();
						}
						auxMaps[part].put(tv, partAuxTerm);
					}
				}
			}
		}

		for (int part = 0; part < ipls.length + 1; part++) {
			@SuppressWarnings("unchecked") // because Java Generics are broken :(
			final HashMap<TermVariable, Term>[] fixedEQs = new HashMap[ipls.length];
			mCheckingSolver.push(1);
			for (final Entry<String, Integer> entry : mInterpolator.mPartitions.entrySet()) {
				if (entry.getValue() == part) {
					mCheckingSolver.assertTerm(theory.term(entry.getKey()));
				}
			}
			for (final Term lit : literals) {
				final Term atom = mInterpolator.getAtom(lit);
				// is this literal negated in the conflict?
				final boolean isNegated = atom == lit;
				final InterpolatorAtomInfo atomTermInfo = mInterpolator.getAtomTermInfo(atom);
				final LitInfo occInfo = mInterpolator.mAtomOccurenceInfos.get(atom);
				if (occInfo.contains(part)) {
					// Purify literal and replace purification variable by fresh term.
					final Term purLit = purifyAndFix(lit, purVarToTerm, purVarToFreshTerm);
					mCheckingSolver.assertTerm(theory.not(purLit));
				} else if (occInfo.isBLocal(part)) {
					// nothing to do, literal cannot be mixed in sub-tree.
				} else if (occInfo.isALocalInSomeChild(part)) {
					// nothing to do, literal cannot be mixed in node
					// or some direct children
				} else if (atomTermInfo.isCCEquality()) {
					// handle mixed (dis)equalities.
					final ApplicationTerm cceq = atomTermInfo.getEquality();
					int firstMixedChild = -1;
					int secondMixedChild = -1;
					for (int child = part - 1; child >= mInterpolator.mStartOfSubtrees[part];
							child = mInterpolator.mStartOfSubtrees[child] - 1) {
						if (occInfo.isMixed(child)) {
							if (firstMixedChild < 0) {
								firstMixedChild = child;
							} else {
								assert secondMixedChild < 0;
								secondMixedChild = child;
							}
						}
					}
					// now lhs is the auxvar of the child that contains lhs, or lhs if part contains it
					// rhs is the auxvar of the child that contains rhs, or rhs if part contains it
					if (firstMixedChild < 0) {
						// we are the partition where one of the aux variables resides.
						assert occInfo.isMixed(part);
						final String op = isNegated ? Interpolator.EQ : "=";
						final int side = occInfo.getLhsOccur().isALocal(part) ? 0 : 1;
						final Term auxvar = auxMaps[part].get(occInfo.mMixedVar);
						mCheckingSolver.assertTerm(theory.term(op, auxvar, cceq.getParameters()[side]));
					} else if (!occInfo.isMixed(part)) {
						final Term auxvar = auxMaps[firstMixedChild].get(occInfo.mMixedVar);
						if (secondMixedChild < 0) {
							final int side = occInfo.getLhsOccur().isALocal(firstMixedChild) ? 1 : 0;
							if (isNegated) {
								mCheckingSolver.assertTerm(
										theory.not(theory.term(Interpolator.EQ, auxvar, cceq.getParameters()[side])));
							} else {
								mCheckingSolver.assertTerm(theory.term("=", auxvar, cceq.getParameters()[side]));
							}
						} else {
							if (fixedEQs[secondMixedChild] == null) {
								fixedEQs[secondMixedChild] = new HashMap<>();
							}
							// replace EQ in second mixed child by the negated eq of first child.
							fixedEQs[secondMixedChild].put(occInfo.mMixedVar,
									theory.not(theory.term(Interpolator.EQ, auxvar, occInfo.mMixedVar)));
						}
					} else {
						assert firstMixedChild >= 0 && secondMixedChild < 0 && occInfo.isMixed(part);
						// nothing to do for intermediate partitions
					}
				} else if (atomTermInfo.isLAEquality() && isNegated) {
					// handle mixed LA disequalities.
					final InterpolatorAffineTerm at = new InterpolatorAffineTerm();
					int firstMixedChild = -1;
					for (int child = part
							- 1; child >= mInterpolator.mStartOfSubtrees[part]; child = mInterpolator.mStartOfSubtrees[child]
									- 1) {
						if (occInfo.isMixed(child)) {
							at.add(Rational.MONE, occInfo.getAPart(child));
							if (firstMixedChild < 0) {
								firstMixedChild = child;
							} else {
								final Term auxvar = auxMaps[child].get(occInfo.mMixedVar);
								at.add(Rational.ONE, auxvar);
								if (fixedEQs[child] == null) {
									fixedEQs[child] = new HashMap<>();
								}
								// replace EQ in other mixed child by equality -- TODO can we do better?
								// this will not find all bugs in interpolation lemmas.
								fixedEQs[child].put(occInfo.mMixedVar, theory.term("=", auxvar, occInfo.mMixedVar));
							}
						}
					}
					// now lhs is the auxvar of the child that contains lhs, or lhs if part contains it
					// rhs is the auxvar of the child that contains rhs, or rhs if part contains it
					if (occInfo.isMixed(part)) {
						// we are the partition where one of the aux variables resides.
						assert occInfo.isMixed(part);
						at.add(Rational.ONE, occInfo.getAPart(part));
						if (firstMixedChild < 0) {
							final Term auxvar = auxMaps[part].get(occInfo.mMixedVar);
							final Term aPart = at.toSMTLib(theory, atomTermInfo.isInt());
							mCheckingSolver.assertTerm(theory.term(Interpolator.EQ, auxvar, aPart));
						} else {
							// replace EQ(xparent, s) with EQ(xchild, s - aparent).
							final Term auxvar = auxMaps[firstMixedChild].get(occInfo.mMixedVar);
							at.negate();
							at.add(Rational.ONE, occInfo.mMixedVar);
							if (fixedEQs[part] == null) {
								fixedEQs[part] = new HashMap<>();
							}
							final Term replacement =
									theory.term(Interpolator.EQ, auxvar, at.toSMTLib(theory, atomTermInfo.isInt()));
							fixedEQs[part].put(occInfo.mMixedVar, replacement);
						}
					} else {
						assert firstMixedChild >= 0;
						final Term auxvar = auxMaps[firstMixedChild].get(occInfo.mMixedVar);
						at.add(Rational.ONE, atomTermInfo.getAffineTerm());
						at.negate();
						final Term bPart = at.toSMTLib(theory, atomTermInfo.isInt());
						mCheckingSolver.assertTerm(theory.not(theory.term(Interpolator.EQ, auxvar, bPart)));
					}
				} else {
					// handle mixed LA inequalities and equalities.

					// check if literal is mixed in part or some child partition.
					final InterpolatorAffineTerm at = new InterpolatorAffineTerm();
					for (int child = part
							- 1; child >= mInterpolator.mStartOfSubtrees[part]; child = mInterpolator.mStartOfSubtrees[child]
									- 1) {
						if (occInfo.isMixed(child)) {
							// child and node are A-local.
							at.add(Rational.MONE, occInfo.getAPart(child));
							at.add(Rational.ONE, auxMaps[child].get(occInfo.mMixedVar));
						}
					}
					if (occInfo.isMixed(part)) {
						assert occInfo.mMixedVar != null;
						at.add(Rational.ONE, occInfo.getAPart(part));
						at.add(Rational.MONE, auxMaps[part].get(occInfo.mMixedVar));
					} else {
						final InterpolatorAffineTerm lv = new InterpolatorAffineTerm(atomTermInfo.getAffineTerm());
						// handle the inverse bound for negated literals
						if (isNegated) {
							lv.add(atomTermInfo.getEpsilon().negate());
						}
						at.add(Rational.ONE, lv);
					}
					if (atomTermInfo.isBoundConstraint()) {
						if (isNegated) {
							at.negate();
						}
						mCheckingSolver.assertTerm(at.toLeq0(theory));
					} else {
						final boolean isInt = at.isInt();
						final Sort sort = theory.getSort(isInt ? "Int" : "Real");
						final Term t = at.toSMTLib(theory, isInt);
						final Term zero = Rational.ZERO.toTerm(sort);
						Term eqTerm = theory.term("=", t, zero);
						if (!occInfo.isMixed(part) && isNegated) {
							eqTerm = theory.term("not", eqTerm);
						}
						mCheckingSolver.assertTerm(eqTerm);
					}
				}
			}
			for (int child = part - 1; child >= mInterpolator.mStartOfSubtrees[part];
					child = mInterpolator.mStartOfSubtrees[child] - 1) {
				Term interpolant = fixupAndLet(ipls[child], fixedEQs[child], auxMaps[child]);
				// Replace purification variable in interpolant by fresh term.
				interpolant = fixVars(interpolant, purVarToFreshTerm);
				mCheckingSolver.assertTerm(interpolant);
			}

			if (part < ipls.length) {
				Term interpolant = fixupAndLet(ipls[part], fixedEQs[part], auxMaps[part]);
				// Replace purification variable in interpolant by fresh term.
				interpolant = fixVars(interpolant, purVarToFreshTerm);
				mCheckingSolver.assertTerm(theory.not(interpolant));
			}
			// Assert auxeq in all partitions were outermost symbol is contained and/or
			// interpolant contains auxvar.
			for (final Entry<TermVariable, Term> e : purVarToTerm.entrySet()) {
				final ApplicationTerm t = (ApplicationTerm) e.getValue();
				final Occurrence occ = mInterpolator.mFunctionSymbolOccurrenceInfos.get(t.getFunction());
				if (occ.contains(part) || activeVars.contains(e.getKey()) || true) {
					final Term tNew = fixVars(t, purVarToFreshTerm);
					mCheckingSolver.assertTerm(theory.term("=", tNew, purVarToFreshTerm.get(e.getKey())));
				}
			}
			if (mCheckingSolver.checkSat() == LBool.SAT) {
				throw new AssertionError();
			}
			mCheckingSolver.pop(1);
		}
		mCheckingSolver.pop(1);
		logger.setLoglevel(old);
	}

	public void assertUnpartitionedFormulas(final Collection<Term> assertions, final Set<String> partitions) {
		final LogProxy logger = mInterpolator.getLogger();
		final int old = logger.getLoglevel();
		try {
			logger.setLoglevel(LogProxy.LOGLEVEL_ERROR);
			// Clone the current context except for the parts used in the
			// interpolation problem
			final SymbolCollector collector = new SymbolCollector();
			termloop: for (final Term asserted : assertions) {
				if (asserted instanceof AnnotatedTerm) {
					final AnnotatedTerm annot = (AnnotatedTerm) asserted;
					for (final Annotation an : annot.getAnnotations()) {
						if (":named".equals(an.getKey()) && partitions.contains(an.getValue())) {
							continue termloop;
						}
					}
				}
				mCheckingSolver.assertTerm(asserted);
				collector.collect(asserted);
			}
			mGlobals = collector.getSymbols();
		} finally {
			logger.setLoglevel(old);
		}
	}

	public boolean checkFinalInterpolants(final Map<String, Integer> partitions, final Term[] interpolants) {
		boolean error = false;
		final int numPartitions = interpolants.length + 1;

		// Compute the symbol occurrence:
		final SymbolCollector collector = new SymbolCollector();
		@SuppressWarnings("unchecked")
		final Set<FunctionSymbol>[] occs = new Set[numPartitions];
		for (int part = 0; part < numPartitions; part++) {
			for (final Entry<String, Integer> entry : mInterpolator.mPartitions.entrySet()) {
				if (entry.getValue() == part) {
					collector.collect(mCheckingSolver.term(entry.getKey()));
				}
			}
			occs[part] = collector.getSymbols();
		}
		// Compute for each partition, in how many the subpartitions symbol occurs.
		@SuppressWarnings("unchecked")
		final Map<FunctionSymbol, Integer>[] subOccurrences = new Map[numPartitions];
		for (int part = 0; part < numPartitions; ++part) {
			// Find children
			subOccurrences[part] = new HashMap<>();
			for (final FunctionSymbol fsym : occs[part]) {
				subOccurrences[part].put(fsym, 1);
			}
			for (int child = part - 1; child >= mInterpolator.mStartOfSubtrees[part];
					child = mInterpolator.mStartOfSubtrees[child] - 1) {
				// join occurrence maps
				for (final Map.Entry<FunctionSymbol, Integer> entry : subOccurrences[child].entrySet()) {
					Integer ival = subOccurrences[part].get(entry.getKey());
					if (ival == null) {
						ival = 0;
					}
					subOccurrences[part].put(entry.getKey(), ival + entry.getValue());
				}
			}
		}

		final LogProxy logger = mInterpolator.getLogger();
		final int old = logger.getLoglevel();
		try {
			logger.setLoglevel(LogProxy.LOGLEVEL_ERROR);
			final SymbolChecker checker = new SymbolChecker(mGlobals, subOccurrences[interpolants.length]);
			for (int part = 0; part < numPartitions; part++) {
				mCheckingSolver.push(1);
				for (int child = part - 1; child >= mInterpolator.mStartOfSubtrees[part];
						child = mInterpolator.mStartOfSubtrees[child] - 1) {
					// Assert child interpolant
					mCheckingSolver.assertTerm(interpolants[child]);
				}
				// assert input formula
				for (final Entry<String, Integer> entry : mInterpolator.mPartitions.entrySet()) {
					if (entry.getValue() == part) {
						mCheckingSolver.assertTerm(mCheckingSolver.term(entry.getKey()));
					}
				}
				if (part != interpolants.length) {
					// Check symbol condition
					if (checker.check(interpolants[part], subOccurrences[part])) {
						logger.error("Symbol error in Interpolant %d: A-local: %s, B-local: %s.", part,
								checker.getALocals(), checker.getBLocals());
						error = true;
					}
					// Assert negated interpolant
					mCheckingSolver.assertTerm(mCheckingSolver.term("not", interpolants[part]));
				}
				final LBool res = mCheckingSolver.checkSat();
				if (res == LBool.SAT) {
					logger.error("Interpolant %d not inductive", part);
					error = true;
				} else if (res == LBool.UNKNOWN) {
					logger.warn("Unable to check validity of interpolant: %s",
							mCheckingSolver.getInfo(":reason-unknown"));
				}
				mCheckingSolver.pop(1);
			}
		} finally {
			logger.setLoglevel(old);
		}
		return !error;
	}
}
