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
import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class UltimateInterpolator extends WrapperScript {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final HashMap<String, Term> mTermMap;
	private final ArrayList<Set<Term>> mVarList;

	public UltimateInterpolator(final IUltimateServiceProvider services, final ILogger logger, final Script script) {
		super(script);
		mServices = services;
		mLogger = logger;
		mMgdScript = new ManagedScript(services, mScript);
		mTermMap = new HashMap<String, Term>();
		mVarList = new ArrayList<Set<Term>>();
	}
	
	
	/**
	 * This function makes sure that "produce-unsat-cores" is always enabled,
	 * if "produce-interpolants" is set true.
	 */
	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if (":produce-interpolants".equals(opt) && "true".equals((String) value)) {
			super.setOption(":produce-unsat-cores", value);
		} else {
			super.setOption(opt, value);
		}
	}
	
	/**
	 * This function maps term Annotations value (name of term) to
	 * term Annotations subterm (content of term) if the annotation is of sorts :named.
	 */ 
	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annoTerm = (AnnotatedTerm) term;
			if (annoTerm.getAnnotations().length == 0) {
				throw new AssertionError("Term has to have at least one annotation");
			}
			for (Annotation anno: annoTerm.getAnnotations()) {
				if (":named".equals(anno.getKey())) {
					mTermMap.put(anno.getValue().toString(), annoTerm.getSubterm());
				}
			}
		}
		return super.assertTerm(term);
	}
	
	@Override
	public Term[] getInterpolants(Term[] partition, final int[] startOfSubtree) {
		for(int i = 0; i < partition.length; i++) {
			if (!mTermMap.containsKey(partition[i].toString())) {
				throw new UnsupportedOperationException("Interpolation not allowed for " + partition[i]);
			}
		}
		final Term[] uc = mMgdScript.getScript().getUnsatCore();
		final Term[] interpolants = new Term[partition.length - 1];
		getDistinctVariables(partition, uc);
		for (int i = 0; i < partition.length - 1; i++) {
			if (Arrays.asList(uc).contains(partition[i])) {
				final Set<TermVariable> varSet = new HashSet<TermVariable>();
				final HashMap<Term, Term> constantToVar = new HashMap<Term, Term>();
				Term conjunctionTerm;
				for (Term t: mVarList.get(i)) {
					TermVariable var = mMgdScript.getScript().variable(t.toString(), t.getSort());
					varSet.add(var);
					constantToVar.put(t, var);
				}
				final Term t = mTermMap.get(partition[i].toString());
				if (i == 0) {
					conjunctionTerm = t;
				} else {
					conjunctionTerm = SmtUtils.and(mMgdScript.getScript(), t, interpolants[i - 1]);
				}
				if (!varSet.isEmpty()) {
					final Term substitutedTerm = Substitution.apply(mMgdScript.getScript(), constantToVar,
							conjunctionTerm);
					conjunctionTerm = SmtUtils.quantifier(mMgdScript.getScript(),
							QuantifiedFormula.EXISTS, varSet, substitutedTerm);
					final Script protectAssertions = new ProtectiveScript(mMgdScript.getScript());
					final ManagedScript mgdAssertionScript = new ManagedScript(mServices, protectAssertions);
					conjunctionTerm = PartialQuantifierElimination.eliminateLight(mServices, 
							mgdAssertionScript, conjunctionTerm);
				}
				interpolants[i] = conjunctionTerm;
			}  else if (i == 0) {
				interpolants[i] = mMgdScript.getScript().term("true");
			} else {
				interpolants[i] = interpolants[i - 1];
			}
		}
		return interpolants;
	}

	/**
	 * This function fills up mVarList at position i with variables
	 * that only occur up to the i'th term in the partition.
	 * 
	 * Optimize with uc so that only terms of the partition are considered
	 * that are part of the uc.
	 * 
	 * Also respect theory, i.e. only add variable if its not part of theory extension.
	 * 
	 * @param partition
	 * @param uc
	 */
	private void getDistinctVariables(final Term[] partition, final Term[] uc) {
		final ArrayList<Set<Term>> theoryExtension = getConstants(uc, partition, false);
		final ArrayList<Set<Term>> overwriteArray = getConstants(partition, uc, true);
		for (int i = 0; i < overwriteArray.size() - 1; i++) {
			mVarList.add(new HashSet<Term>());
			for (Term t: overwriteArray.get(i)) {
				final Boolean occOverwrite = checkOccurrence(overwriteArray, t, i);
				final Boolean occTheory = checkOccurrence(theoryExtension, t, -1);
				if (Boolean.TRUE.equals(occOverwrite == false) && Boolean.TRUE.equals(occTheory == false)) {
					mVarList.get(i).add(t);
				}
			}
		}
		mVarList.add(new HashSet<Term>());
	}
	
	/**
	 * Check occurrence of term t in List consts.
	 * 
	 * @param consts Arraylist of Set of Terms
	 * @param t Term to search for
	 * @param i index
	 * @return true if term t occurs in one of the Sets of the Arraylist from index i + 1 onwards. Otherwise false.
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
	 * Function to return constants of Terms occuring in A and B. If reverse flag is set false, return
	 * constants of Terms only occuring in A.
	 * 
	 * @param setA Array of Terms
	 * @param setB Array of Terms
	 * @param reverse flag
	 * @return Described constants in ArrayList of Sets of Terms
	 */
	private ArrayList<Set<Term>> getConstants(final Term[] setA, final Term[] setB, Boolean reverse) {
		final ArrayList<Set<Term>> result = new ArrayList<Set<Term>>();
		for (int i = 0; i < setA.length; i++) {
			final Term nameTerm = setA[i];
			if (Arrays.asList(setB).contains(nameTerm) == Boolean.TRUE.equals(reverse)) {
				final Set<Term> subTerm = SubTermFinder.find((ApplicationTerm) mTermMap.get(nameTerm.toString()),
						new CheckForSubterm(), false);
				result.add(subTerm);
			} else {
				result.add(new HashSet<Term>());
			}
		}
		return result;
	}
	
	/**
	 * Predicate is used to get all constant symbols in a term
	 * that are an ApplicationTerm.
	 */
	public static class CheckForSubterm implements Predicate<Term> {
		@Override
		public boolean test(Term t) {
			if (t instanceof ApplicationTerm) {
				if (((ApplicationTerm) t).getParameters().length == 0) {
					return true;
				}
			}
			return false;
		}
	}


}
