/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.AssertCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DeclareFunCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DefineFunCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.ISmtCommand;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class UltimateInterpolator extends WrapperScript {

	final static TermVariable[] EMPTY_TERM_VARIABLE_ARRAY = {};

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final HashMap<String, Term> mTermMap;
	private final ArrayList<Set<Term>> mVarList;
	private int mFunCount;
	private int mCountAsserts;
	private int mCountPush;
	private int mCountDeclaredFuns;
	private final Deque<ISmtCommand<Void>> mAssertStack;
	private final Deque<Triple<Integer, Pair<Integer, Integer>, Integer>> mLastPush;
	private final boolean mCheckInterpolants;

	public UltimateInterpolator(final IUltimateServiceProvider services, final ILogger logger, final Script script) {
		super(script);
		mServices = services;
		mLogger = logger;
		mMgdScript = new ManagedScript(services, mScript);
		mTermMap = new HashMap<String, Term>();
		mVarList = new ArrayList<Set<Term>>();
		mFunCount = 0;
		mCountPush = 0;
		mCountAsserts = 0;
		mCountDeclaredFuns = 0;
		mAssertStack = new LinkedList<ISmtCommand<Void>>();
		mLastPush = new LinkedList<Triple<Integer, Pair<Integer, Integer>, Integer>>();
		mCheckInterpolants = true;
	}

	/**
	 * This method makes sure that "produce-unsat-cores" is always enabled, if
	 * "produce-interpolants" is set true.
	 */
	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if (":produce-interpolants".equals(opt) && "true".equals((String) value)) {
			super.setOption(":produce-unsat-cores", value);
		} else {
			super.setOption(opt, value);
		}
		super.setOption(":interactive-mode", true);
	}

	/**
	 * Set Logic to allow quantifiers.
	 */
	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
	}
	
	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		mScript.push(1);
		mCountDeclaredFuns++;
		mAssertStack.push(new DeclareFunCommand(fun, paramSorts, resultSort));
		super.declareFun(fun, paramSorts, resultSort);
	}

	/**
	 * This method maps term Annotations value (name of term) to term Annotations
	 * subterm (content of term) if the annotation is of sorts :named. Also keeps
	 * track of assertion commands in mAssertStack and if its an assertion for an
	 * annotated term, keeps track of the define fun command in mFunStack.
	 */
	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mScript.push(1);
		mCountAsserts++;
		mAssertStack.push(new AssertCommand(term));
		if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annoTerm = (AnnotatedTerm) term;
			if (annoTerm.getAnnotations().length == 0) {
				throw new AssertionError("Term has to have at least one annotation");
			}
			for (Annotation anno : annoTerm.getAnnotations()) {
				if (":named".equals(anno.getKey())) {
					mTermMap.put(anno.getValue().toString(), annoTerm.getSubterm());
				}
			}
		}
		return super.assertTerm(term);
	}

	/********************Section to regulate number of push and pop operation*********************/
	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		mScript.push(1);
		mFunCount++;
		return super.annotate(t, annotations);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		if (levels > 0) {
			mLastPush.push(new Triple<>(levels,
					new Pair<Integer, Integer>(mCountAsserts, mCountDeclaredFuns), mFunCount));
			mCountPush = mCountPush + levels;
		}
		super.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		assert levels <= mCountPush;
		super.pop(levels + regulatePop(levels));
	}

	private int regulatePop(final int levels) {
		int sum = 0;
		mCountPush = mCountPush - levels;
		for (int i = 0; i < levels; i++) {
			Triple<Integer, Pair<Integer, Integer>, Integer> top = mLastPush.pop();
			final int abs = top.getSecond().getFirst() + top.getSecond().getSecond();
			for (int j = 0; j < (mCountAsserts + mCountDeclaredFuns) - abs; j++) {
				mAssertStack.pop();
			}
			sum += (mCountAsserts + mCountDeclaredFuns) - abs + mFunCount - top.getThird();
			mFunCount = top.getThird();
			mCountAsserts = top.getSecond().getFirst();
			mCountDeclaredFuns = top.getSecond().getSecond();
			if (top.getFirst() - 1 > 0) {
				mLastPush.push(new Triple<>(top.getFirst() - 1,
						new Pair<Integer, Integer>(mCountAsserts, mCountDeclaredFuns), mFunCount));
			}
		}
		return sum;
	}

	/*********************************************************************************************/

	@Override
	public Term[] getInterpolants(Term[] partition, final int[] startOfSubtree) {
		for (int i = 0; i < partition.length; i++) {
			final Set<Term> subTerm = SubTermFinder.find((ApplicationTerm) partition[i], new CheckForSubterm(), false);
			for (Term t : subTerm) {
				if (!mTermMap.containsKey(t.toString())) {
					throw new UnsupportedOperationException("Interpolation not allowed for " + t);
				}
			}
		}
		final Term[] uc = mMgdScript.getScript().getUnsatCore();
		removeAssertions();
		addDeclaredFuns();
		final Term[] interpolants = new Term[partition.length - 1];
		getDistinctVariables(partition, uc);
		for (int i = 0; i < partition.length - 1; i++) {
			final Term[] ar = { partition[i] };
			final ArrayList<Term> tList = getFunsymbols(ar);
			if (!Collections.disjoint(Arrays.asList(uc), tList)) {
				final Set<TermVariable> varSet = new HashSet<TermVariable>();
				final HashMap<Term, Term> constantToVar = new HashMap<Term, Term>();
				Term conjunctionTerm;
				for (Term t : mVarList.get(i)) {
					String str = SmtUtils.removeSmtQuoteCharacters(t.toString());
					TermVariable var = mMgdScript.getScript().variable(str, t.getSort());
					varSet.add(var);
					constantToVar.put(t, var);
				}
				final Term t = buildTerm(partition[i], tList);
				if (i == 0) {
					conjunctionTerm = t;
				} else {
					conjunctionTerm = SmtUtils.and(mMgdScript.getScript(), t, interpolants[i - 1]);
				}
				if (!varSet.isEmpty()) {
					final Term substitutedTerm = Substitution.apply(mMgdScript.getScript(), constantToVar,
							conjunctionTerm);
					conjunctionTerm = SmtUtils.quantifier(mMgdScript.getScript(), QuantifiedFormula.EXISTS, varSet,
							substitutedTerm);
					// for eliminate: SimplificationTechnique.SIMPLIFY_DDA2
					conjunctionTerm = PartialQuantifierElimination.eliminateLight(mServices, mMgdScript,
							conjunctionTerm);
				}
				interpolants[i] = conjunctionTerm;
			} else if (i == 0) {
				interpolants[i] = mMgdScript.getScript().term("true");
			} else {
				interpolants[i] = interpolants[i - 1];
			}
		}
		if (mCheckInterpolants) {
			assert checkInterpolants(interpolants, partition, uc);
		}
		removeDeclaredFuns();
		addAssertions();
		return interpolants;
	}

	/*
	 * Builds the term for the formula in the partition.
	 */
	private Term buildTerm(Term partition, ArrayList<Term> funSymbs) {
		final HashMap<Term, Term> symbToFormula = new HashMap<Term, Term>();
		for (Term t : funSymbs) {
			symbToFormula.put(t, mTermMap.get(t.toString()));
		}
		final Term result = Substitution.apply(mScript, symbToFormula, partition);
		return result;
	}

	/**
	 * Method to remove assertions from script mScript.
	 */
	private void removeAssertions() {
		mScript.pop(mFunCount + mCountAsserts + mCountPush + mCountDeclaredFuns);
	}

	/**
	 * Method to add removed assertions and function symbols back to script mScript.
	 */
	private void addAssertions() {
		int counter = 0;
		ListIterator<ISmtCommand<Void>> value = ((LinkedList<ISmtCommand<Void>>) mAssertStack)
				.listIterator(mAssertStack.size());
		ListIterator<Triple<Integer, Pair<Integer, Integer>, Integer>> it =
				((LinkedList<Triple<Integer, Pair<Integer, Integer>, Integer>>) mLastPush)
				.listIterator(mLastPush.size());
		while (value.hasPrevious()) {
			if (it.hasPrevious()) {
				final Triple<Integer, Pair<Integer, Integer>, Integer> trip = it.previous();
				if (trip.getSecond().getFirst() + trip.getSecond().getSecond() == counter) {
					mScript.push(trip.getFirst());
				} else {
					it.next();
				}
			}
			mScript.push(1);
			final ISmtCommand<Void> cmd = value.previous();
			cmd.executeWithScript(mScript);
			if (cmd instanceof AssertCommand) {
				if (((AssertCommand) cmd).getTerm() instanceof AnnotatedTerm) {
					addFun((AnnotatedTerm) ((AssertCommand) cmd).getTerm(), mScript);
				}
			}
			counter++;
		}
		assert mScript.checkSat() == LBool.UNSAT;
	}
	
	/*
	 * Method to add declared function symbols to properly use them while generating interpolants.
	 */
	private void addDeclaredFuns() {
		mScript.push(1);
		for (ISmtCommand<Void> cmd: mAssertStack) {
			if (cmd instanceof DeclareFunCommand) {
				cmd.executeWithScript(mScript);
			}
		}
	}
	
	/*
	 * Removes declared funs that were only added to generate interpolants.
	 */
	private void removeDeclaredFuns() {
		mScript.pop(1);
	}

	/**
	 * Method to add annotation to term annoT as function symbol to script mScript.
	 */
	private void addFun(AnnotatedTerm annoT, Script script) {
		for (Annotation anno : annoT.getAnnotations()) {
			mScript.push(1);
			final DefineFunCommand funCmd = new DefineFunCommand(anno.getValue().toString(), EMPTY_TERM_VARIABLE_ARRAY,
					annoT.getSubterm().getSort(), annoT.getSubterm());
			funCmd.executeWithScript(script);
		}
	}

	/**
	 * This method fills up mVarList at position i with variables that only occur up
	 * to the i'th term in the partition.
	 * 
	 * Optimize with uc so that only terms of the partition are considered that are
	 * part of the uc.
	 * 
	 * Also respect theory, i.e. only add variable if its not part of theory
	 * extension.
	 * 
	 * @param partition
	 * @param uc
	 */
	private void getDistinctVariables(final Term[] partition, final Term[] uc) {
		final ArrayList<Set<Term>> theoryExtension = getConstants(uc, partition, false);
		final ArrayList<Set<Term>> overwriteArray = getConstants(partition, uc, true);
		final ArrayList<Set<Term>> otherTheory = makeTheory();
		for (int i = 0; i < overwriteArray.size() - 1; i++) {
			mVarList.add(new HashSet<Term>());
			for (Term t : overwriteArray.get(i)) {
				final Boolean occOverwrite = checkOccurrence(overwriteArray, t, i);
				final Boolean occTheory = checkOccurrence(theoryExtension, t, -1);
				final Boolean occOtherTheory = checkOccurrence(otherTheory, t, -1);
				if (Boolean.TRUE.equals(occOverwrite == false) && Boolean.TRUE.equals(occTheory == false)
						&& Boolean.TRUE.equals(occOtherTheory == false)) {
					mVarList.get(i).add(t);
				}
			}
		}
		mVarList.add(new HashSet<Term>());
	}

	/**
	 * Check occurrence of term t in List consts. True if term t occurs in one of
	 * the Sets of the Arraylist from index i + 1 onwards. Otherwise false.
	 */
	private static Boolean checkOccurrence(final ArrayList<Set<Term>> consts, final Term t, final int i) {
		for (int j = i + 1; j < consts.size(); j++) {
			if (consts.get(j).contains(t)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Method to return constants of Terms occuring in setA and setB. If reverse
	 * flag is set false, return constants of Terms only occuring in setA.
	 */
	private ArrayList<Set<Term>> getConstants(final Term[] setA, final Term[] setB, Boolean reverse) {
		final ArrayList<Set<Term>> result = new ArrayList<Set<Term>>();
		final ArrayList<Term> funSymB = getFunsymbols(setB);
		for (int i = 0; i < setA.length; i++) {
			result.add(new HashSet<Term>());
			final Term[] ar = { setA[i] };
			final ArrayList<Term> nameTerm = getFunsymbols(ar);
			for (Term t : nameTerm) {
				if (funSymB.contains(t) == Boolean.TRUE.equals(reverse)) {
					final Set<Term> subTerm = SubTermFinder.find((ApplicationTerm) mTermMap.get(t.toString()),
							new CheckForSubterm(), false);
					result.get(i).addAll(subTerm);
				}
			}
		}
		return result;
	}

	/**
	 * Returns all constants that are part of a term, which is not a named term.
	 */
	private ArrayList<Set<Term>> makeTheory() {
		final ArrayList<Set<Term>> result = new ArrayList<Set<Term>>();
		for (ISmtCommand<Void> t : mAssertStack) {
			if (t instanceof AssertCommand) {
				final Term temp = ((AssertCommand) t).getTerm();
				if (!(temp instanceof AnnotatedTerm)) {
					final Set<Term> subTerm = SubTermFinder.find(temp, new CheckForSubterm(), false);
					result.add(subTerm);
				}
			}
		}
		return result;
	}

	/*
	 * Returns all function symbols that are part of any term in the partition.
	 */
	private ArrayList<Term> getFunsymbols(final Term[] partition) {
		Set<Term> result = new HashSet<Term>();
		for (int i = 0; i < partition.length; i++) {
			final Set<Term> subTerm = SubTermFinder.find((ApplicationTerm) partition[i], new CheckForSubterm(), false);
			for (Term t : subTerm) {
				if (mTermMap.containsKey(t.toString())) {
					result.add(t);
				}
			}
		}
		return new ArrayList<Term>(result);
	}

	/**
	 * Method to check if the produced interpolants are correct.
	 */
	private boolean checkInterpolants(Term[] interpolants, Term[] partition, Term[] uc) {
		/*
		 * Number of interpolants (n - 1) needs to be 1 less than number of terms in
		 * partition (n)
		 */
		if (interpolants.length != partition.length - 1) {
			return false;
		}

		/* Add theory onto assertion stack */
		int theoryPushes = 0;
		final ArrayList<Term> partSyms = getFunsymbols(partition);
		for (ISmtCommand<Void> t : mAssertStack) {
			if (t instanceof AssertCommand) {
				final Term temp = ((AssertCommand) t).getTerm();
				if (!(temp instanceof AnnotatedTerm)) {
					theoryPushes++;
					mScript.push(1);
					t.executeWithScript(mScript);
				}
			}
		}
		for (Term t : uc) {
			if (!(partSyms.contains(t))) {
				final Term theo = mTermMap.get(t.toString());
				theoryPushes++;
				mScript.push(1);
				mScript.assertTerm(theo);
			}
		}

		/* F_1 \land \lnot I_1 needs to be unsat */
		final Term[] ar = { partition[0] };
		final ArrayList<Term> fOneSyms = getFunsymbols(ar);
		final Term fOne = buildTerm(partition[0], fOneSyms);
		final Term notIOne = SmtUtils.not(mScript, interpolants[0]);
		mScript.push(1);
		mScript.assertTerm(SmtUtils.and(mScript, notIOne, fOne));
		if (mScript.checkSat() == LBool.SAT) {
			return false;
		}
		mScript.pop(1);

		/* F_n \land I_n needs to be unsat */
		final Term[] arr = { partition[partition.length - 1] };
		final ArrayList<Term> fEnSyms = getFunsymbols(arr);
		final Term fEn = buildTerm(partition[partition.length - 1], fEnSyms);
		mScript.push(1);
		mScript.assertTerm(SmtUtils.and(mScript, fEn, interpolants[interpolants.length - 1]));
		if (mScript.checkSat() == LBool.SAT) {
			return false;
		}
		mScript.pop(1);

		/*
		 * I_{i-1} \land F_i \land \lnot I_i needs to be unsat for all i, 2 <= i <= n-1
		 */
		for (int i = 1; i < partition.length - 1; i++) {
			final Term intIMinus = interpolants[i - 1];
			final Term[] arra = { partition[i] };
			final ArrayList<Term> fISyms = getFunsymbols(arra);
			final Term formI = buildTerm(partition[i], fISyms);
			final Term notIntI = SmtUtils.not(mScript, interpolants[i]);
			mScript.push(1);
			mScript.assertTerm(SmtUtils.and(mScript, intIMinus, formI, notIntI));
			if (mScript.checkSat() == LBool.SAT) {
				return false;
			}
			mScript.pop(1);
		}
		if (theoryPushes > 0) {
			mScript.pop(theoryPushes);
		}
		return true;
	}

	/**
	 * Predicate is used to get all constant symbols in a term that are an
	 * ApplicationTerm.
	 */
	public static class CheckForSubterm implements Predicate<Term> {
		@Override
		public boolean test(Term t) {
			if (t instanceof ApplicationTerm) {
				if (((ApplicationTerm) t).getParameters().length == 0
						&& !("true".equals(t.toString()) || "false".equals(t.toString()))) {
					return true;
				}
			}
			return false;
		}
	}

}
