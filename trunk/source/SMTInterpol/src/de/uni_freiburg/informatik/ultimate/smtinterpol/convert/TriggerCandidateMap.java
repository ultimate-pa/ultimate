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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.CollectionsHelper;

public class TriggerCandidateMap {
	private final LogProxy mLogger;
	private final HashMap<FunctionSymbol, List<ApplicationTerm>> mFuncs;
	private final Set<ApplicationTerm> mUnitCandidates;
	private final Theory mTheory;
	private Set<TermVariable> mVars;
	public TriggerCandidateMap(LogProxy logger,Theory theory,
			Set<TermVariable> vars) {
		mLogger = logger;
		mFuncs = new HashMap<FunctionSymbol,List<ApplicationTerm>>();
		// We need insertion order iterators since we want to extract minimal
		// candidates first. Inserting child before parent guarantees this.
		mUnitCandidates = new LinkedHashSet<ApplicationTerm>();
		mTheory = theory;
		mVars = vars;
	}
	
	public void insert(Term term) {
		assert term.getSort() == mTheory.getBooleanSort() :	"Inserting non-boolean term";
		// Remove let terms and lift term-ites...
		final InferencePreparation ip = new InferencePreparation(mTheory,mVars);
		recinsert(ip.prepare(term));
	}
	// return true iff term contains an internal subterm
	private boolean recinsert(Term term) {
		if (term.getFreeVars() == null || term.getFreeVars().length == 00) {
			return false;
		}
		if (term instanceof AnnotatedTerm) {
			term = ((AnnotatedTerm)term).getSubterm();
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm fat = (ApplicationTerm)term;
			final Term[] params = fat.getParameters();
			boolean internal = false;
			for (final Term param : params) {
				internal |= recinsert(param);
			}
			if (internal) {
				return true;
			}
			final FunctionSymbol fs = fat.getFunction();
			if (isFunctionAllowedInTrigger(fs)) {
				List<ApplicationTerm> fapps = mFuncs.get(fs);
				if (fapps == null) {
					fapps = new ArrayList<ApplicationTerm>();
					mFuncs.put(fs, fapps);
				}
				if (mVars.containsAll(Arrays.asList(
						term.getFreeVars()))) {
					mUnitCandidates.add(fat);
				}
				fapps.add(fat);
				return false;
			}
			return true;
		}
		return false;
	}
	/**
	 * Can this function contribute to a trigger. We allow all non-internal 
	 * symbols, equality and the select and store array internals. 
	 * @param fs Function symbol to check.
	 * @return <code>true</code> if and only if <code>fs</code> can contribute.
	 */
	private final boolean isFunctionAllowedInTrigger(FunctionSymbol fs) {
		return !fs.isIntern() || fs.getName().equals("=") 
			|| fs.getName().equals("select") || fs.getName().equals("store");
	}

	public boolean isLoopingPattern(ApplicationTerm candidate) {
		final List<ApplicationTerm> fapps = mFuncs.get(candidate.getFunction());
		assert (fapps != null) : "Pattern candidate does not occur in the sub";
		for (final ApplicationTerm at : fapps) {
			if (at == candidate) {
				continue;
			}
			if (hasVarMatchError(candidate,at)) {
				mLogger.debug("Pattern candidate %s dropped. It is looping against %s...",
								candidate,at);
				return true;
			}
		}
		return false;
	}
	private boolean hasVarMatchError(Term candidate,
			Term fat) {
		if (candidate instanceof TermVariable && !(fat instanceof TermVariable)) {
			return fat.getFreeVars() != null
			    && Arrays.asList(fat.getFreeVars()).contains(candidate);
		}
		if (candidate instanceof ApplicationTerm
		        && fat instanceof ApplicationTerm) {
			final ApplicationTerm capp = (ApplicationTerm)candidate;
			final ApplicationTerm fapp = (ApplicationTerm)fat;
			if (capp.getFunction() == fapp.getFunction()) {
				final Term[] cparams = capp.getParameters();
				final Term[] fparams = fapp.getParameters();
				assert(cparams.length == fparams.length);
				for (int i = 0; i < cparams.length; ++i) {
					if (hasVarMatchError(cparams[i], fparams[i])) {
						return true;
					}
				}
			}
		}
		return false;
	}
	/**
	 * Infer <strong>one</strong> multi trigger.
	 * @return Multi trigger or <code>null</code> if none could be inferred.
	 */
	public Term[] getMultiTrigger() { // NOPMD
		int trigsize = 2;
		while (trigsize <= mVars.size()) {
			final Set<Term> trigs = getMultiTrigger(trigsize);
			if (trigs != null) {
				assert(trigs.size() == trigsize);
				return trigs.toArray(new Term[trigs.size()]);
			}
			++trigsize;
		}
		return null;
	}
	private Set<Term> getMultiTrigger(int trigsize) {
		final HashSet<TermVariable> uncovered =
			new HashSet<TermVariable>(mVars.size(),1);
		uncovered.addAll(mVars);
		final HashSet<Term> candidate = new HashSet<Term>(trigsize,1);
		for (final List<ApplicationTerm> fapps : mFuncs.values()) {
			for (final ApplicationTerm fat : fapps) {
				candidate.add(fat);
				assert(fat.getFreeVars() != null && fat.getFreeVars().length != 0);
				final Collection<TermVariable> termVars =
					Arrays.asList(fat.getFreeVars());
				uncovered.removeAll(termVars);
				if (completeMultiTrigger(candidate,uncovered,trigsize - 1)) {
					return candidate;
				}
				uncovered.addAll(termVars);
				candidate.remove(fat);
			}
		}
		return null;
	}
	private boolean completeMultiTrigger(HashSet<Term> candidate,
			HashSet<TermVariable> uncovered,int trigsize) {
		if (trigsize == 0) {
			return uncovered.isEmpty();
		}
		for (final List<ApplicationTerm> fapps : mFuncs.values()) {
			for (final ApplicationTerm fat : fapps) {
				final Collection<TermVariable> tvs =
					Arrays.asList(fat.getFreeVars());
				if (!CollectionsHelper.containsAny(uncovered,tvs)) {
					// Would not reduce the problem...
					continue;
				}
				if (!candidate.add(fat)) {
					continue;
				}
				uncovered.removeAll(tvs);
				if (completeMultiTrigger(candidate,uncovered,trigsize - 1)) {
					return true;
				}
				uncovered.addAll(tvs);
				candidate.remove(fat);
			}
		}
		return false;
	}
	/**
	 * Infer <strong>all possible</strong> unit-triggers.
	 * 
	 *  Looping pattern are blocked iff 
	 *  ConvertFormula.FEATURE_BLOCK_LOOPING_PATTERN is true.
	 * @return All possible unit triggers.
	 */
	public Term[] getAllUnitTriggers() {
		final HashSet<Term> unittrigs = new HashSet<Term>();
		final HashSet<Term> considered = new HashSet<Term>();
	candidates: 
	    for (final ApplicationTerm c : mUnitCandidates) {
	        for (final Term t : c.getParameters()) {
				// All term with at least on considered children are considered as well...
				if (considered.contains(t)) {
					considered.add(c);
					continue candidates;
				}
			}
			final TermVariable[] fvars = c.getFreeVars();
			final HashSet<TermVariable> vars = 
				new HashSet<TermVariable>(fvars.length,1);
			for (final TermVariable tv : fvars) {
				vars.add(tv);
			}
			if (vars.equals(mVars) 
					&& (!Config.FEATURE_BLOCK_LOOPING_PATTERN 
					        || !isLoopingPattern(c))) {
				// Consider this candidate
				unittrigs.add(c);
				considered.add(c);
			}
		}
		return unittrigs.isEmpty()
		        ? null : unittrigs.toArray(new Term[unittrigs.size()]);
	}
	/**
	 * Reinitialize this map for inference for a different set of variables.
	 * Note that you have to reinsert all terms.
	 * @param vars Variable to infer pattern for.
	 */
	public void reinit(Set<TermVariable> vars) {
		mFuncs.clear();
		mUnitCandidates.clear();
		mVars = vars;
	}
}
