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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.CollectionsHelper;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class TriggerCandidateMap {
	private Logger mlogger;
	private HashMap<FunctionSymbol, List<ApplicationTerm>> m_funcs;
	private Set<ApplicationTerm> m_unitCandidates;
	private Theory m_theory;
	private Set<TermVariable> m_vars;
	public TriggerCandidateMap(Logger logger,Theory theory,
			Set<TermVariable> vars) {
		mlogger = logger;
		m_funcs = new HashMap<FunctionSymbol,List<ApplicationTerm>>();
		// We need insertion order iterators since we want to extract minimal
		// candidates first. Inserting child before parent guarantees this.
		m_unitCandidates = new LinkedHashSet<ApplicationTerm>();
		m_theory = theory;
		m_vars = vars;
	}
	
	public void insert(Term term) {
		assert term.getSort() == m_theory.getBooleanSort() : 
			"Inserting non-boolean term";
		// Remove let terms and lift term-ites...
		InferencePreparation ip = new InferencePreparation(m_theory,m_vars);
		recinsert(ip.prepare(term));
	}
	// return true iff term contains an internal subterm
	private boolean recinsert(Term term) {
		if (term.getFreeVars() == null || term.getFreeVars().length == 00)
			return false;
		if (term instanceof AnnotatedTerm)
			term = ((AnnotatedTerm)term).getSubterm();
		if (term instanceof ApplicationTerm) {
			ApplicationTerm fat = (ApplicationTerm)term;
			Term[] params = fat.getParameters();
			boolean internal = false;
			for (Term param : params)
				internal |= recinsert(param);
			if (internal)
				return true;
			FunctionSymbol fs = fat.getFunction();
			if (isFunctionAllowedInTrigger(fs)) {
				List<ApplicationTerm> fapps = m_funcs.get(fs);
				if (fapps == null) {
					fapps = new ArrayList<ApplicationTerm>();
					m_funcs.put(fs, fapps);
				}
				if (m_vars.containsAll(Arrays.asList(
						term.getFreeVars())))
					m_unitCandidates.add(fat);
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
		return !fs.isIntern() || fs.getName().equals("=") || 
			fs.getName().equals("select") || fs.getName().equals("store");
	}

	public boolean isLoopingPattern(ApplicationTerm candidate) {
		List<ApplicationTerm> fapps = m_funcs.get(candidate.getFunction());
		assert (fapps != null) : "Pattern candidate does not occur in the sub";
		for (ApplicationTerm at : fapps) {
			if (at == candidate)
				continue;
			if (hasVarMatchError(candidate,at)) {
				mlogger.debug(
						new DebugMessage(
								"Pattern candidate {0} dropped. It is looping against {1}...",
								candidate,at));
				return true;
			}
		}
		return false;
	}
	private boolean hasVarMatchError(Term candidate,
			Term fat) {
		if (candidate instanceof TermVariable && 
				!(fat instanceof TermVariable))
			return fat.getFreeVars() != null &&
					Arrays.asList(fat.getFreeVars()).
						contains(candidate);
		if (candidate instanceof ApplicationTerm &&
				fat instanceof ApplicationTerm) {
			ApplicationTerm capp = (ApplicationTerm)candidate;
			ApplicationTerm fapp = (ApplicationTerm)fat;
			if (capp.getFunction() == fapp.getFunction()) {
				Term[] cparams = capp.getParameters();
				Term[] fparams = fapp.getParameters();
				assert(cparams.length == fparams.length);
				for (int i = 0; i < cparams.length; ++i) {
					if (hasVarMatchError(cparams[i], fparams[i]))
						return true;
				}
			}
		}
		return false;
	}
	/**
	 * Infer <strong>one</strong> multi trigger.
	 * @return Multi trigger or <code>null</code> if none could be inferred.
	 */
	public Term[] getMultiTrigger() {
		int trigsize = 2;
		while (trigsize <= m_vars.size()) {
			Set<Term> trigs = getMultiTrigger(trigsize);
			if (trigs != null) {
				assert(trigs.size() == trigsize);
				return trigs.toArray(new Term[trigs.size()]);
			}
			++trigsize;
		}
		return null;
	}
	private Set<Term> getMultiTrigger(int trigsize) {
		HashSet<TermVariable> uncovered =
			new HashSet<TermVariable>(m_vars.size(),1);
		uncovered.addAll(m_vars);
		HashSet<Term> candidate = new HashSet<Term>(trigsize,1);
		for (List<ApplicationTerm> fapps : m_funcs.values()) {
			for (ApplicationTerm fat : fapps) {
				candidate.add(fat);
				assert(fat.getFreeVars() != null && fat.getFreeVars().length != 0);
				Collection<TermVariable> termVars =
					Arrays.asList(fat.getFreeVars());
				uncovered.removeAll(termVars);
				if (completeMultiTrigger(candidate,uncovered,trigsize - 1))
					return candidate;
				uncovered.addAll(termVars);
				candidate.remove(fat);
			}
		}
		return null;
	}
	private boolean completeMultiTrigger(HashSet<Term> candidate,
			HashSet<TermVariable> uncovered,int trigsize) {
		if (trigsize == 0)
			return uncovered.isEmpty();
		for (List<ApplicationTerm> fapps : m_funcs.values()) {
			for (ApplicationTerm fat : fapps) {
				Collection<TermVariable> tvs =
					Arrays.asList(fat.getFreeVars());
				if (!CollectionsHelper.containsAny(uncovered,tvs))
					// Would not reduce the problem...
					continue;
				if (!candidate.add(fat))
					continue;
				uncovered.removeAll(tvs);
				if (completeMultiTrigger(candidate,uncovered,trigsize - 1))
					return true;
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
		HashSet<Term> unittrigs = new HashSet<Term>();
		HashSet<Term> considered = new HashSet<Term>();
		candidates: for (ApplicationTerm c : m_unitCandidates) {
			for (Term t : c.getParameters())
				// All term with at least on considered children are considered as well...
				if (considered.contains(t)) {
					considered.add(c);
					continue candidates;
				}
			TermVariable[] fvars = c.getFreeVars();
			HashSet<TermVariable> vars = 
				new HashSet<TermVariable>(fvars.length,1);
			for (TermVariable tv : fvars)
				vars.add(tv);
			if (vars.equals(m_vars) && 
					(!Config.FEATURE_BLOCK_LOOPING_PATTERN || 
							!isLoopingPattern(c))) {
				// Consider this candidate
				unittrigs.add(c);
				considered.add(c);
			}
		}
		return unittrigs.isEmpty() ? 
				null : unittrigs.toArray(new Term[unittrigs.size()]);
	}
	/**
	 * Reinitialize this map for inference for a different set of variables.
	 * Note that you have to reinsert all terms.
	 * @param vars Variable to infer pattern for.
	 */
	public void reinit(Set<TermVariable> vars) {
		m_funcs.clear();
		m_unitCandidates.clear();
		m_vars = vars;
	}
}
	