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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class UltimateInterpolator extends WrapperScript {

	final static TermVariable[] EMPTY_TERM_VARIABLE_ARRAY = {};

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	protected final Script mSupportingScript;
	private final ManagedScript mMgdScript;
	private final ManagedScript mSupMgdScript;
	private final HashMap<String, Term> mTermMap;
	private final HashMap<Integer, Integer> mCurrentSubtree;
	private final HashMap<Integer, ArrayList<Integer>> mIncludesNodes;
	private final boolean mCheckInterpolants;
	private final TermTransferrer mTransferrer;
	private final TermTransferrer mReTransferrer;

	public UltimateInterpolator(final IUltimateServiceProvider services, final ILogger logger,
			final Script script, final Script supportScript) {
		super(script);
		mServices = services;
		mLogger = logger;
		mSupportingScript = supportScript;
		mMgdScript = new ManagedScript(services, mScript);
		mSupMgdScript = new ManagedScript(services, mSupportingScript);
		mTermMap = new HashMap<String, Term>();
		mCurrentSubtree = new HashMap<Integer, Integer>();
		mIncludesNodes = new HashMap<Integer, ArrayList<Integer>>();
		mCheckInterpolants = false;
		mTransferrer = new TermTransferrer(mScript, mSupportingScript);
		mReTransferrer = new TermTransferrer(mSupportingScript, mScript);
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
		mSupportingScript.setOption(":interactive-mode", true);
	}

	/**
	 * Set Logic for supporting script.
	 */
	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
		mSupportingScript.setLogic(logic);
	}

	/**
	 * This method maps term Annotations value (name of term) to term Annotations
	 * subterm (content of term) if the annotation is of sorts :named. Also keeps
	 * track of assertion commands in mAssertStack and if its an assertion for an
	 * annotated term, keeps track of the define fun command in mFunStack.
	 */
	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
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
	
	/* Used for inductive sequences of interpolants */
	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		final Term[] uc = mScript.getUnsatCore();
		final Term[] interpolants = combinedMethod(partition, uc);
		if (mCheckInterpolants) {
			assert checkInterpolants(interpolants, partition, uc);
		}
		return interpolants;
	}

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
		// Produce sequence of interpolants if startOfSubtree only contains zeros
		if (containsOnlyZeros(startOfSubtree)) {
			return getInterpolants(partition);
		}
		final Term[] interpolants = new Term[partition.length - 1];
		// ArrayList<Set<Term>> constants = writeConstants(partition);
		for (int i = 0; i < partition.length - 1; i++) {
			final Term[] ar = { partition[i] };
			final ArrayList<Term> fIsyms = getFunsymbols(ar);
			final Term formulaI = buildTerm(partition[i], fIsyms);
			final ArrayList<Set<Term>> otherTheory = makeTheory();
			Set<Term> mergedSet = new HashSet<>();
	        for (Set<Term> set : otherTheory) {
	            mergedSet.addAll(set);
	        }
			if (startOfSubtree[i] == i) {
				mCurrentSubtree.put(i, i);
				ArrayList<Integer> list = new ArrayList<Integer>();
				list.add(i);
				mIncludesNodes.put(i, list);
				interpolants[i] = quantifyEliminate(formulaI, i, startOfSubtree, partition, mergedSet);
				continue;
			}
			if (startOfSubtree[i] == startOfSubtree[i - 1]) {
				mCurrentSubtree.put(startOfSubtree[i], i);
				mIncludesNodes.get(startOfSubtree[i]).add(i);
				interpolants[i] = quantifyEliminate(SmtUtils.and(mScript, formulaI, interpolants[i - 1]),
						i, startOfSubtree, partition, mergedSet);
			} else {
				mIncludesNodes.get(startOfSubtree[i]).add(i);
				interpolants[i] = quantifyEliminate(closeSubtrees(interpolants, formulaI, i, startOfSubtree),
						i, startOfSubtree, partition, mergedSet);
			}
			
		}
		return interpolants;
	}
	
	/* quantifies variables that only occur in subtree and also eliminates quantifiers afterwards */
	private Term quantifyEliminate(Term conjunction, int i, int[] startOfSubtree, Term[] partition,
			Set<Term> theoryVars) {
		// get all Constant symbols in subtree and outside subtree
		final Set<Term> subTreeConstants = new HashSet<Term>();
		final Set<Term> otherTreeConstants = new HashSet<Term>();
		final ArrayList<Term> subTree = new ArrayList<Term>();
		final ArrayList<Term> otherTrees = new ArrayList<Term>();
		for (Map.Entry<Integer, ArrayList<Integer>> entry: mIncludesNodes.entrySet()) {
			if (entry.getKey() >= startOfSubtree[i]) {
				for (Integer k: entry.getValue()) {
					subTree.add(partition[k]);
					final Term[] ar = { partition[k] };
					final ArrayList<Term> fsyms = getFunsymbols(ar);
					subTreeConstants.addAll(SubTermFinder.find((ApplicationTerm) buildTerm(partition[k], fsyms),
							new CheckForSubterm(), false));
				}
			}
		}
		for (Term t: partition) {
			if (!subTree.contains(t)) {
				otherTrees.add(t);
				final Term[] ar = { t };
				final ArrayList<Term> fsyms = getFunsymbols(ar);
				otherTreeConstants.addAll(SubTermFinder.find((ApplicationTerm) buildTerm(t, fsyms),
						new CheckForSubterm(), false));
			}
		}
		// determine all constant symbols that only occur in subtree but not outside subtree
		final HashMap<Term, Term> constantToVar = new HashMap<Term, Term>();
		final Set<TermVariable> varSet = new HashSet<TermVariable>();
		for (Term t: subTreeConstants) {
			if (!otherTreeConstants.contains(t) && !theoryVars.contains(t)) {
				String str = SmtUtils.removeSmtQuoteCharacters(t.toString());
				TermVariable var = mScript.variable(str, t.getSort());
				varSet.add(var);
				constantToVar.put(t, var);
			}
		}
		// quantify these constant symbols and eliminate quantifiers
		if (!varSet.isEmpty()) {
			final Term substitutedTerm = Substitution.apply(mScript, constantToVar,
					conjunction);
			conjunction = SmtUtils.quantifier(mScript, QuantifiedFormula.EXISTS, varSet,
					substitutedTerm);
			final Term transTerm = mTransferrer.transform(conjunction);
			// for eliminate: SimplificationTechnique.SIMPLIFY_DDA2
			final Term transElim = PartialQuantifierElimination.eliminateLight(mServices, mSupMgdScript,
					transTerm);
			conjunction = mReTransferrer.transform(transElim);
		}
		return conjunction;
	}
	
	/* Builds interpolant for a node i in the tree that has more than one child, by constructing the conjunction of
	 * the interpolants of its children and the partition formula at node i.*/
	private Term closeSubtrees(Term[] interpolants, Term formulaI, int i, int[] sOS) {
		Term interpolant = formulaI;
		ArrayList<Integer> toRemove = new ArrayList<Integer>();
		for (Map.Entry<Integer, Integer> entry: mCurrentSubtree.entrySet()) {
			if (entry.getKey() >= sOS[i]) {
				interpolant = SmtUtils.and(mScript, interpolant, interpolants[entry.getValue()]);
				toRemove.add(entry.getKey());
			}
		}
		for (Integer key: toRemove) {
			mCurrentSubtree.remove(key);
		}
		mCurrentSubtree.put(sOS[i], i);
		return interpolant;
	}
	
	/* Checks whether the array arr only contains zeros */
	private static boolean containsOnlyZeros(int[] arr) {
	    for (int i = 0; i < arr.length; i++) {
	        if (arr[i] != 0) {
	            return false;
	        }
	    }
	    return true;
	}
	
	/** Combines sequence of interpolants using existential quantifier and sequence using universal quantifier
	 *  in order to minimize amount of quantifiers in resulting sequence of interpolants. **/
	private Term[] combinedMethod(Term[] partition, Term[] uc) {
		final Term[] exInterpolants = existentialSequence(partition, uc);
		final Term[] allInterpolants = forallSequence(partition, uc);
		final Term[] interpolants = new Term[partition.length - 1];
		final int[] exValues = new int[exInterpolants.length];
		final int[] allValues = new int[allInterpolants.length];
		for (int i = 0; i < exValues.length; i++) {
			/** evaluate interpolant by counting nested quantifiers **/
			exValues[i] = recFunc(exInterpolants[i], 0, new LinkedList<Integer>());
			allValues[i] = recFunc(allInterpolants[i], 0, new LinkedList<Integer>());
		}
		final int breakNumber = smallestNumber(exValues, allValues);
		for (int i = 0; i < allInterpolants.length; i++) {
			interpolants[i] = i < breakNumber ? exInterpolants[i] : allInterpolants[i];
		}
		return interpolants;
	}
	
	/* testing new recursive heuristic method to evaluate interpolant */
	private static int recFunc(Term interpolant, int h, LinkedList<Integer> quantifiers) {
		if (interpolant instanceof ApplicationTerm) {
			Term[] param = ((ApplicationTerm) interpolant).getParameters();
			if (param.length == 0) {
				return h;
			}
			for (Term t: param) {
				h = recFunc(t, h, quantifiers);
			}
		} else if (interpolant instanceof QuantifiedFormula) {
			Term subForm = ((QuantifiedFormula) interpolant).getSubformula();
			int quantifier = ((QuantifiedFormula) interpolant).getQuantifier();
			if (quantifiers.isEmpty()) {
				h = h + 2;
			} else {
				int last = quantifiers.getLast();
				if (quantifier == last) {
					h = h + 2;
				} else {
					h = h * 2;
				}
			}
			quantifiers.add(quantifier);
			h = recFunc(subForm, h, quantifiers);
		}
		return h;
	}
	
	/**
	 * @param exNumbers are the mapped heuristic values for existential interpolants
	 * @param allNumbers are the mapped heuristic values for universal interpolants
	 * @return integer i that is index where sum of heuristic values from existential interpolants up to
	 * (but not including) i and the sum of heuristic values starting from (including) i to the end.
	 */
	private static int smallestNumber(int[] exNumbers, int[] allNumbers) {
		int index = -1;
		if (exNumbers.length <= 0 || exNumbers.length != allNumbers.length) {
			return index;
		}
		int min = IntStream.of(exNumbers).sum() + 1;
		for (int i = 0; i < exNumbers.length + 1; i++) {
			int value = 0;
			for (int j = 0; j < exNumbers.length; j++) {
				value = j < i ? (value + exNumbers[j]) : (value + allNumbers[j]);
			}
			if (value <= min) {
				min = value;
				index = i;
			}
		}
		return index;
	}

	/** Calls method to generate interpolants using existential quantifier **/
	private Term[] existentialSequence(Term[] partition, Term[] uc) {
		return genericInterpolants(partition, uc, false);
	}

	/** Calls method to generate interpolants using universal quantifier **/
	private Term[] forallSequence(Term[] partition, Term[] uc) {
		final List<Term> list = Arrays.asList(partition);
		Collections.reverse(list);
		final Term[] reversedPartition = list.toArray(new Term[0]);
		Term[] interpolants = genericInterpolants(reversedPartition, uc, true);
		final List<Term> reInterpolants = Arrays.asList(interpolants);
		Collections.reverse(reInterpolants);
		Collections.reverse(list);
		return interpolants;
	}
	
	/** Can be used to generate interpolants using either universal or existential quantifier **/
	private Term[] genericInterpolants(Term[] partition, Term[] uc, boolean universalFlag) {
		final Term[] interpolants = new Term[partition.length - 1];
		final ArrayList<Set<Term>> varList;
		varList = getDistinctVariables(partition, uc);
		for (int i = 0; i < partition.length - 1; i++) {
			final Term[] ar = { partition[i] };
			final ArrayList<Term> tList = getFunsymbols(ar);
			if (!Collections.disjoint(Arrays.asList(uc), tList)) {
				final Set<TermVariable> varSet = new HashSet<TermVariable>();
				final HashMap<Term, Term> constantToVar = new HashMap<Term, Term>();
				Term conjunctionTerm;
				for (Term t : varList.get(i)) {
					String str = SmtUtils.removeSmtQuoteCharacters(t.toString());
					TermVariable var = mScript.variable(str, t.getSort());
					varSet.add(var);
					constantToVar.put(t, var);
				}
				final Term t = buildTerm(partition[i], tList);
				if (i == 0) {
					conjunctionTerm = universalFlag ? SmtUtils.not(mScript, t) : t;
				} else {
					conjunctionTerm = universalFlag ? SmtUtils.or(mScript, SmtUtils.not(mScript, t),
							interpolants[i - 1]) : SmtUtils.and(mScript, t, interpolants[i - 1]);
				}
				if (!varSet.isEmpty()) {
					final Term substitutedTerm = Substitution.apply(mScript, constantToVar,
							conjunctionTerm);
					conjunctionTerm = universalFlag ? SmtUtils.quantifier(mScript, QuantifiedFormula.FORALL, varSet,
							substitutedTerm) : SmtUtils.quantifier(mScript, QuantifiedFormula.EXISTS, varSet,
							substitutedTerm);
					final Term transTerm = mTransferrer.transform(conjunctionTerm);
					// for eliminate: SimplificationTechnique.SIMPLIFY_DDA2
					final Term transElim = PartialQuantifierElimination.eliminateLight(mServices, mSupMgdScript,
							transTerm);
					conjunctionTerm = mReTransferrer.transform(transElim);
				}
				interpolants[i] = conjunctionTerm;
			} else if (i == 0) {
				interpolants[i] = universalFlag ? mScript.term("false") : mScript.term("true");
			} else {
				interpolants[i] = interpolants[i - 1];
			}
		}
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
	private ArrayList<Set<Term>> getDistinctVariables(final Term[] partition, final Term[] uc) {
		final ArrayList<Set<Term>> varList = new ArrayList<Set<Term>>();
		final ArrayList<Set<Term>> theoryExtension = getConstants(uc, partition, false);
		final ArrayList<Set<Term>> overwriteArray = getConstants(partition, uc, true);
		final ArrayList<Set<Term>> otherTheory = makeTheory();
		for (int i = 0; i < overwriteArray.size() - 1; i++) {
			varList.add(new HashSet<Term>());
			for (Term t : overwriteArray.get(i)) {
				final Boolean occOverwrite = checkOccurrence(overwriteArray, t, i);
				final Boolean occTheory = checkOccurrence(theoryExtension, t, -1);
				final Boolean occOtherTheory = checkOccurrence(otherTheory, t, -1);
				if (Boolean.TRUE.equals(occOverwrite == false) && Boolean.TRUE.equals(occTheory == false)
						&& Boolean.TRUE.equals(occOtherTheory == false)) {
					varList.get(i).add(t);
				}
			}
		}
		varList.add(new HashSet<Term>());
		return varList;
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
		for (Term t : mScript.getAssertions()) {
			if (!(t instanceof AnnotatedTerm)) {
				final Set<Term> subTerm = SubTermFinder.find(t, new CheckForSubterm(), false);
				result.add(subTerm);
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
		
		/* Push once on supporting script to remove all assertions at the end of interpolant check */
		mSupportingScript.push(1);

		/* Add theory onto assertion stack */
		for (Term t : mScript.getAssertions()) {
			if (!(t instanceof AnnotatedTerm)) {
				mSupportingScript.assertTerm(mTransferrer.transform(t));
			}
		}
		
		final ArrayList<Term> partSyms = getFunsymbols(partition);
		for (Term t : uc) {
			if (!(partSyms.contains(t))) {
				final Term theo = mTermMap.get(t.toString());
				mSupportingScript.assertTerm(mTransferrer.transform(theo));
			}
		}

		/* F_1 \land \lnot I_1 needs to be unsat */
		final Term[] ar = { partition[0] };
		final ArrayList<Term> fOneSyms = getFunsymbols(ar);
		final Term fOne = buildTerm(partition[0], fOneSyms);
		final Term notIOne = SmtUtils.not(mScript, interpolants[0]);
		mSupportingScript.push(1);
		mSupportingScript.assertTerm(mTransferrer.transform(SmtUtils.and(mScript, notIOne, fOne)));
		if (mSupportingScript.checkSat() == LBool.SAT) {
			return false;
		}
		mSupportingScript.pop(1);

		/* F_n \land I_n needs to be unsat */
		final Term[] arr = { partition[partition.length - 1] };
		final ArrayList<Term> fEnSyms = getFunsymbols(arr);
		final Term fEn = buildTerm(partition[partition.length - 1], fEnSyms);
		mSupportingScript.push(1);
		mSupportingScript.assertTerm(mTransferrer.transform(SmtUtils.and(mScript, fEn,
				interpolants[interpolants.length - 1])));
		if (mSupportingScript.checkSat() == LBool.SAT) {
			return false;
		}
		mSupportingScript.pop(1);

		/*
		 * I_{i-1} \land F_i \land \lnot I_i needs to be unsat for all i, 2 <= i <= n-1
		 */
		for (int i = 1; i < partition.length - 1; i++) {
			final Term intIMinus = interpolants[i - 1];
			final Term[] arra = { partition[i] };
			final ArrayList<Term> fISyms = getFunsymbols(arra);
			final Term formI = buildTerm(partition[i], fISyms);
			final Term notIntI = SmtUtils.not(mScript, interpolants[i]);
			mSupportingScript.push(1);
			mSupportingScript.assertTerm(mTransferrer.transform(SmtUtils.and(mScript, intIMinus, formI, notIntI)));
			if (mSupportingScript.checkSat() == LBool.SAT) {
				return false;
			}
			mSupportingScript.pop(1);
		}
		mSupportingScript.pop(1);
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
	
	/**
	 * Predicate that is used to get quantifiers in term.
	 */
	public static class CheckForQuantifier implements Predicate<Term> {
		@Override
		public boolean test(Term t) {
			if (t instanceof QuantifiedFormula) {
				return true;
			}
			return false;
		}
	}

}
