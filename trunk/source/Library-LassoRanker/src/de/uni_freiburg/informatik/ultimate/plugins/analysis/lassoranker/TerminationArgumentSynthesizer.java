/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.RankingFunctionTemplate;


/**
 * This is the synthesizer that generates ranking functions.
 * 
 * @author Jan Leike
 */
class TerminationArgumentSynthesizer {
	
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * SMT script for the template instance
	 */
	private final Script m_script;
	
	// Stem and loop transitions as linear inequalities in DNF
	private final LinearTransition m_stem;
	private final LinearTransition m_loop;
	
	/**
	 * List of supporting invariant generators used by the last synthesize()
	 * call
	 */
	private final Collection<SupportingInvariantGenerator> m_si_generators;
	
	/**
	 * Whether synthesize() has been called yet
	 */
	private boolean m_synthesized = false;
	
	/**
	 * Number of Motzkin's Theorem applications used by the last synthesize()
	 * call
	 */
	private int m_num_motzkin = 0;
	
	// Objects resulting from the synthesis process
	private RankingFunction m_ranking_function = null;
	private Collection<SupportingInvariant> m_supporting_invariants = null;
	
	public final Preferences m_preferences;
	
	/**
	 * Constructor for the termination argument function synthesizer.
	 * @param script SMT Solver
	 * @param stem the stem transition, may be null
	 * @param loop the loop transition
	 * @param preferences arguments to the synthesis process
	 */
	public TerminationArgumentSynthesizer(Script script, LinearTransition stem,
			LinearTransition loop, Preferences preferences) {
		m_preferences = preferences;
		m_script = script;
		m_si_generators = new ArrayList<SupportingInvariantGenerator>();
		
		// Set logic
		script.reset();
		if (preferences.termination_check_nonlinear) {
			script.setLogic(Logics.QF_NRA);
		} else {
			script.setLogic(Logics.QF_LRA);
		}
		
		m_supporting_invariants = new ArrayList<SupportingInvariant>();
		
		if (stem == null) {
			m_stem = LinearTransition.getTranstionTrue();
		} else {
			m_stem = stem;
		}
		m_loop = loop;
	}
	
	/**
	 * @return RankVar's that are relevant for supporting invariants
	 */
	private Collection<RankVar> getSIVars() {
		/*
		 * Variables that occur as outVars of the stem but are not read by the
		 * loop (i.e., do not occur as inVar of the loop) are not relevant for
		 * supporting invariants.
		 */
		if (m_stem == null) {
			return Collections.emptyList();
		}
		Set<RankVar> result =
				new LinkedHashSet<RankVar>(m_stem.getOutVars().keySet());
		result.retainAll(m_loop.getInVars().keySet());
		return result;
	}
	
	/**
	 * @return RankVar's that are relevant for ranking functions
	 */
	private Collection<RankVar> getRankVars() {
		Collection<RankVar> vars = 
				new LinkedHashSet<RankVar>(m_loop.getOutVars().keySet());
		vars.retainAll(m_loop.getInVars().keySet());
		return vars;
	}
	
	/**
	 * Use the ranking template to build the constraints whose solution gives
	 * the termination argument
	 * @param template the ranking function template
	 * @param si_generators Output container for the used SI generators
	 * @return List of all conjuncts of the constraints
	 */
	private Collection<Term> buildConstraints(RankingFunctionTemplate template,
			Collection<SupportingInvariantGenerator> si_generators) {
		List<Term> conj = new ArrayList<Term>(); // List of constraints
		
		Collection<RankVar> siVars = getSIVars();
		List<List<LinearInequality>> templateConstraints =
				template.constraints(m_loop.getInVars(),
						m_loop.getOutVars());
		List<String> annotations = template.getAnnotations();
		assert annotations.size() == templateConstraints.size();
		
		s_Logger.info("We have " + m_loop.getNumPolyhedra()
				+ " loop disjuncts and " + templateConstraints.size()
				+ " template conjuncts.");
		
		// Negate template inequalities
		for (List<LinearInequality> templateDisj : templateConstraints) {
			for (LinearInequality li : templateDisj) {
				li.negate();
			}
		}
		
		// loop(x, x') /\ si(x) -> template(x, x')
		// Iterate over the loop conjunctions and template disjunctions
		int j = 0;
		for (List<LinearInequality> loopConj : m_loop.getPolyhedra()) {
			++j;
			for (int m = 0; m < templateConstraints.size(); ++m) {
				MotzkinTransformation motzkin =
						new MotzkinTransformation(m_script,
								!m_preferences.termination_check_nonlinear,
								m_preferences.annotate_terms);
				motzkin.annotation = annotations.get(m) + " " + j;
				motzkin.add_inequalities(loopConj);
				motzkin.add_inequalities(templateConstraints.get(m));
				
				// Add supporting invariants
				assert(m_preferences.num_strict_invariants >= 0);
				for (int i = 0; i < m_preferences.num_strict_invariants; ++i) {
					SupportingInvariantGenerator sig =
							new SupportingInvariantGenerator(m_script, siVars,
									true);
					si_generators.add(sig);
					motzkin.add_inequality(sig.generate(m_loop.getInVars()));
				}
				assert(m_preferences.num_non_strict_invariants >= 0);
				for (int i = 0; i < m_preferences.num_non_strict_invariants;
						++i) {
					SupportingInvariantGenerator sig =
							new SupportingInvariantGenerator(m_script, siVars,
									false);
					si_generators.add(sig);
					LinearInequality li = sig.generate(m_loop.getInVars());
					li.motzkin_coefficient_can_be_zero = false;
					motzkin.add_inequality(li);
				}
				s_Logger.debug(motzkin);
				conj.add(motzkin.transform());
			}
		}
		
		// Add constraints for the supporting invariants
		s_Logger.debug("Adding the constraints for " + si_generators.size()
				+ " supporting invariants.");
		int i = 0;
		for (SupportingInvariantGenerator sig : si_generators) {
			++i;
			
			// stem(x0) -> si(x0)
			j = 0;
			for (List<LinearInequality> stemConj : m_stem.getPolyhedra()) {
				++j;
				MotzkinTransformation motzkin =
						new MotzkinTransformation(m_script,
								!m_preferences.termination_check_nonlinear,
								m_preferences.annotate_terms);
				motzkin.annotation = "invariant " + i + " initiation " + j;
				motzkin.add_inequalities(stemConj);
				LinearInequality li = sig.generate(m_stem.getOutVars());
				li.negate();
				li.motzkin_coefficient_can_be_zero = false;
					// otherwise the stem is unsat
				motzkin.add_inequality(li);
				conj.add(motzkin.transform());
			}
			
			// si(x) /\ loop(x, x') -> si(x')
			j = 0;
			for (List<LinearInequality> loopConj : m_loop.getPolyhedra()) {
				++j;
				MotzkinTransformation motzkin =
						new MotzkinTransformation(m_script,
								!m_preferences.termination_check_nonlinear,
								m_preferences.annotate_terms);
				motzkin.annotation = "invariant " + i + " consecution " + j;
				motzkin.add_inequalities(loopConj);
				motzkin.add_inequality(sig.generate(m_loop.getInVars())); // si(x)
				LinearInequality li = sig.generate(m_loop.getOutVars()); // ~si(x')
				li.needs_motzkin_coefficient =
						!m_preferences.only_nondecreasing_invariants;
				li.negate();
				motzkin.add_inequality(li);
				conj.add(motzkin.transform());
			}
		}
		return conj;
	}
	
	/**
	 * Ranking function generation for lasso programs
	 * 
	 * This procedure is complete in the sense that if there is a linear ranking
	 * function that can be derived with a linear supporting invariant of the
	 * form si(x) >= 0, then it will be found by this procedure.
	 * 
	 * Iff a ranking function is found, this method returns true and the
	 * resulting ranking function and supporting invariant can be retrieved
	 * using the methods getRankingFunction() and getSupportingInvariant().
	 * 
	 * @param template the ranking template to be used
	 * @return SAT if a termination argument was found, UNSAT if existence of
	 *  a termination argument was refuted, UNKNOWN if the solver was not able
	 *  to decide existence of a termination argument
	 * @throws SMTLIBException error with the SMT solver
	 * @throws TermException if the supplied transitions contain
	 *          non-affine update statements
	 */
	public LBool synthesize(RankingFunctionTemplate template)
			throws SMTLIBException, TermException {
		assert !m_synthesized;
		m_synthesized = true;
		if (!m_preferences.termination_check_nonlinear
				&& template.getDegree() > 0) {
			s_Logger.warn("Using a linear SMT query and a templates of degree "
					+ "> 0, hence this method is incomplete.");
		}
		Collection<RankVar> rankVars = getRankVars();
		Collection<RankVar> siVars = getSIVars();
		template.init(m_script, rankVars,
				!m_preferences.termination_check_nonlinear);
		s_Logger.debug("Variables for ranking functions: " + rankVars);
		s_Logger.debug("Variables for supporting invariants: " + siVars);
/*		// The following code makes examples like StemUnsat.bpl fail
		if (siVars.isEmpty()) {
			s_Logger.info("There is no variables for invariants; "
					+ "disabling supporting invariant generation.");
			m_preferences.num_strict_invariants = 0;
			m_preferences.num_non_strict_invariants = 0;
		} */
		if (m_stem == null) {
			s_Logger.info("There is no stem transition; "
					+ "disabling supporting invariant generation.");
			m_preferences.num_strict_invariants = 0;
			m_preferences.num_non_strict_invariants = 0;
		}
		
		// Assert all conjuncts generated from the template
		Collection<Term> constraints =
				buildConstraints(template, m_si_generators);
		m_num_motzkin = constraints.size();
		s_Logger.info("We have " + getNumMotzkin()
				+ " Motzkin's Theorem applications.");
		s_Logger.info("A total of " + getNumSIs()
				+ " supporting invariants were added.");
		for (Term constraint : constraints) {
			m_script.assertTerm(constraint);
		}
		
		// Check for a model
		LBool sat = m_script.checkSat();
		if (sat == LBool.SAT) {
			s_Logger.debug("Found a model, " +
					"proceeding to extract ranking function.");
			
			// Extract ranking function
			Map<Term, Rational> val_rf =
					AuxiliaryMethods.preprocessValuation(m_script.getValue(
							template.getVariables().toArray(new Term[0])));
			m_ranking_function = template.extractRankingFunction(val_rf);
			
			// Extract supporting invariants
			for (SupportingInvariantGenerator sig : m_si_generators) {
				Map<Term, Rational> val_si =
						AuxiliaryMethods.preprocessValuation(m_script.getValue(
								sig.getVariables().toArray(new Term[0])));
				m_supporting_invariants.add(sig.extractSupportingInvariant(
						val_si));
			}
		} else if (sat == LBool.UNKNOWN) {
			// Problem: If we use the following line we can receive the 
			// following response which is not SMTLIB2 compliant.
			// (:reason-unknown canceled)
			// Object reason = m_script.getInfo(":reason-unknown");
		}
		return sat;
	}
	
	/**
	 * @return the number of supporting invariants used
	 */
	public int getNumSIs() {
		assert m_synthesized : "Call synthesize() first";
		return m_si_generators.size();
	}
	
	/**
	 * @return the number of Motzkin's Theorem applications
	 */
	public int getNumMotzkin() {
		assert m_synthesized : "Call synthesize() first";
		return m_num_motzkin;
	}
	
	
	public TerminationArgument getArgument() {
		return new TerminationArgument(m_ranking_function,
				m_supporting_invariants);
	}
}
