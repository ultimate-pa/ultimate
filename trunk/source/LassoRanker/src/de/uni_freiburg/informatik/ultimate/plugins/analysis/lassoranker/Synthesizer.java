package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;
import java.util.Map.Entry;
import java.io.FileNotFoundException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Preferences.UseDivision;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Preferences.VariableDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.DNF;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.InequalityConverter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.IntegralHull;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteEquality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.RankingFunctionTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;


/**
 * This is the synthesizer that generates ranking functions.
 * 
 * @author Jan Leike
 */
public class Synthesizer {
	
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * Prefix for auxiliary variables introduced for integer division
	 */
	private static final String s_auxPrefix = "aux_";
	
	/**
	 * SMT script of the transition formulae
	 */
	private Script m_old_script;
	
	/**
	 * SMT script for the template instance
	 */
	private Script m_script;
	
	// Stem and loop transitions for the linear lasso program
	private TransFormula m_stem_transition;
	private TransFormula m_loop_transition;
	
	// Stem and loop transitions as linear inequalities in DNF
	private List<List<LinearInequality>> m_stem;
	private List<List<LinearInequality>> m_loop;
	
	// Objects resulting from the synthesis process
	private RankingFunction m_ranking_function = null;
	private Collection<SupportingInvariant> m_supporting_invariants = null;
	
	private int m_auxNameIndex;
	
	private Collection<TermVariable> m_auxVars;
	
	/**
	 * Create a new SMT solver instance.
	 * Accesses the RCFGBuilder preferences for solver settings.
	 */
	private Script newScript() {
		// This code is copied from 
		// de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder
		
		Logger solverLogger = Logger.getLogger("interpolLogger");
		Script script = new Scriptor("z3 -smt2 -in", solverLogger);
		
		TAPreferences taPref = new TAPreferences();
		if (taPref.dumpScript()) {
			String dumpFileName = taPref.dumpPath();
			String fileSep = System.getProperty("file.separator");
			dumpFileName += (dumpFileName.endsWith(fileSep) ? "" : fileSep);
			dumpFileName = dumpFileName + "LassoRanker.smt2";
			// FIXME: add file name
			s_Logger.info("Using temporary smt2 file '" + dumpFileName + "'.");
			try {
				script = new LoggingScript(script, dumpFileName, true);
			} catch (FileNotFoundException e) {
				throw new AssertionError(e);
			}
		}
		
		if (Preferences.annotate_terms) {
			script.setOption(":produce-unsat-cores", true);
		}
		script.setOption(":produce-models", true);
		script.setLogic("QF_NRA"); // non-linear algebraic constraint solving
		return script;
	}
	
	/**
	 * Constructor for the ranking function synthesizer.
	 * @param stem transition formula for the program's stem
	 * @param loop transition formula for the program's loop
	 * @param script SMT Solver
	 * @throws Exception If something goes wrong ;)
	 */
	public Synthesizer(Script old_script, TransFormula stem_transition,
			TransFormula loop_transition) throws Exception {
		m_old_script = old_script;
		m_script = newScript();
		
		m_auxVars = new ArrayList<TermVariable>();
		m_supporting_invariants = new ArrayList<SupportingInvariant>();
		
		m_stem_transition = stem_transition;
		m_loop_transition = loop_transition;
		
		s_Logger.debug("Stem: " + stem_transition);
		s_Logger.debug("Loop: " + loop_transition);
		
		preprocess();
	}
	
	/**
	 * Convert a term into a list of clauses
	 * @param term a term in disjunctive normal form
	 * @return list of clauses
	 */
	private static List<Term> toClauses(Term term) {
		List<Term> l = new ArrayList<Term>();
		if (!(term instanceof ApplicationTerm)) {
			l.add(term);
			return l;
		}
		ApplicationTerm appt = (ApplicationTerm) term;
		if (!appt.getFunction().getName().equals("or")) {
			l.add(term);
			return l;
		}
		for (Term t : appt.getParameters()) {
			l.addAll(toClauses(t));
		}
		return l;
	}
	
	/**
	 * Preprocess the stem and loop transition.
	 * The preprocessing step applies various transformations on the stem
	 * and loop formulae:
	 * rewrite ≠, rewrite division, rewrite booleans, convert to DNF, ...
	 * 
	 * See de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors
	 * @throws TermException
	 */
	private void preprocess() throws TermException {
		s_Logger.info("Start preprocessing the stem and loop formulae.");
		
		Term stem_term = m_stem_transition.getFormula();
		Term loop_term = m_loop_transition.getFormula();
		
		// TODO: refactor more preprocessors
		// TODO: rewrite booleans, rewrite division, integral hull
		/*
		if (Preferences.rewrite_booleans) {
			stem_term = boolsToIneq(stem_term);
			loop_term = boolsToIneq(loop_term);
		}
		
		if (Preferences.use_division == UseDivision.C_STYLE) {
			// Replace integer division
			int i = findMinAuxName(stem.getFormula());
			int j = findMinAuxName(loop.getFormula());
			m_auxNameIndex = i > j ? i : j;
			stem_term = replaceDiv(stem_term);
			loop_term = replaceDiv(loop_term);
		}
		*/
		
		// Rewrite '='
		stem_term = (new RewriteEquality()).process(m_old_script, stem_term);
		loop_term = (new RewriteEquality()).process(m_old_script, loop_term);
		
		// Convert to DNF
		stem_term = (new DNF()).process(m_old_script, stem_term);
		loop_term = (new DNF()).process(m_old_script, loop_term);
		
		// Extract clauses
		Collection<Term> stem_clauses = toClauses(stem_term);
		Collection<Term> loop_clauses = toClauses(loop_term);
		
		if (!Preferences.enable_disjunction &&
				(stem_clauses.size() > 1 || loop_clauses.size() > 1)) {
			throw new UnsupportedOperationException(
					"Support for non-conjunctive lasso programs " +
					"is disabled.");
		}
		
		// Transform the stem and loop transition into linear inequalities
		m_stem = new ArrayList<List<LinearInequality>>();
		for (Term clause : stem_clauses) {
			List<LinearInequality> lli = InequalityConverter.convert(m_old_script, clause);
			if ((Preferences.use_variable_domain == VariableDomain.INTEGERS
					|| Preferences.use_variable_domain == VariableDomain.AUTO_DETECT)
					&& Preferences.compute_integral_hull) {
				lli.addAll(IntegralHull.compute(lli));
			}
			m_stem.add(lli);
		}
		m_loop = new ArrayList<List<LinearInequality>>();
		for (Term clause : loop_clauses) {
			List<LinearInequality> lli = InequalityConverter.convert(m_old_script, clause);
			if ((Preferences.use_variable_domain == VariableDomain.INTEGERS
					|| Preferences.use_variable_domain == VariableDomain.AUTO_DETECT)
					&& Preferences.compute_integral_hull) {
				lli.addAll(IntegralHull.compute(lli));
			}
			m_loop.add(lli);
		}
		s_Logger.debug("Stem transition:\n" + m_stem);
		s_Logger.debug("Loop transition:\n" + m_loop);
		
		s_Logger.info("Done with preprocessing.");
	}
	
	/**
	 * Verify that the preferences are set self-consistent and sensible
	 * Issues a bunch of logger infos and warnings.
	 */
	private void checkPreferences() {
		assert(Preferences.num_supporting_invariants >= 0);
		if (Preferences.num_supporting_invariants == 0) {
			s_Logger.warn("Generation of supporting invariants is disabled.");
		}
		if (!Preferences.check_if_loop_infeasible) {
			s_Logger.warn("Check for loop infeasibility is disabled.");
		}
		if (Preferences.use_division == UseDivision.C_STYLE
				&& !Preferences.enable_disjunction) {
			s_Logger.warn("Using C-style integer division, but support for " +
				"disjunctions is disabled.");
		}
		if ((Preferences.use_variable_domain == VariableDomain.INTEGERS
				|| Preferences.use_variable_domain == VariableDomain.AUTO_DETECT)
				&& Preferences.compute_integral_hull) {
			s_Logger.info("Using integer or mixed integer variable domain, "
					+ "but integral hull computation is disabled.  "
					+ "This will reduce the solution space.");
		}
	}
	
	/**
	 * @return boogie variables that are relevant for supporting invariants
	 */
	private Collection<BoogieVar> getSIVars() { 
		return m_stem_transition.getOutVars().keySet();
	}
	
	/**
	 * @return term variables that are relevant for the loop transition
	 */
	private Collection<TermVariable> getLoopVars() {
		Collection<TermVariable> vars = new HashSet<TermVariable>();
		vars.addAll(m_loop_transition.getInVars().values());
		vars.addAll(m_loop_transition.getOutVars().values());
		vars.addAll(m_loop_transition.getAuxVars());
		vars.addAll(m_auxVars);
		return vars;
	}
	
	/**
	 * @return Boogie variables that are relevant for ranking functions
	 */
	private Collection<BoogieVar> getRankVars() {
		Collection<BoogieVar> vars = new HashSet<BoogieVar>();
		vars.addAll(m_loop_transition.getOutVars().keySet());
		vars.retainAll(m_loop_transition.getInVars().keySet());
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
		
		Collection<BoogieVar> siVars = getSIVars();
		
		Collection<Collection<LinearInequality>> templateConstraints =
				template.constraints(m_loop_transition.getInVars(),
						m_loop_transition.getOutVars());
		
		s_Logger.info("We have " + m_loop.size() + " loop conjunctions and "
				+ templateConstraints.size() + " template disjunctions.");
		
		// loop(x, x') /\ si(x) -> template(x, x')
		// Iterate over the loop conjunctions and template disjunctions
		for (List<LinearInequality> loopConj : m_loop) {
			for (Collection<LinearInequality> templateDisj : templateConstraints) {
				MotzkinTransformation motzkin =
						new MotzkinTransformation(m_script);
				motzkin.annotation = templateDisj.toString();
				
				// Loop inequalities
				for (LinearInequality li : loopConj) {
					motzkin.add_inequality(li);
				}
				// Template inequalities
				for (LinearInequality li : templateDisj) {
					li.negate();
					motzkin.add_inequality(li);
				}
				// Supporting invariants
				assert(Preferences.num_supporting_invariants >= 0);
				for (int i = 0; i < Preferences.num_supporting_invariants; ++ i) {
					SupportingInvariantGenerator sig =
							new SupportingInvariantGenerator(m_script, siVars,
									false); // TODO: strict invariants
					si_generators.add(sig);
					motzkin.add_inequality(sig.generate(
							m_loop_transition.getInVars()));
				}
				s_Logger.debug(motzkin);
				conj.add(motzkin.transform());
			}
		}
		
		
		// Add constraints for the supporting invariants
		for (SupportingInvariantGenerator sig : si_generators) {
			// stem(x0) -> si(x0)
			for (List<LinearInequality> stemConj : m_stem) {
				MotzkinTransformation motzkin =
						new MotzkinTransformation(m_script);
				
				for (LinearInequality li : stemConj) {
					motzkin.add_inequality(li);
				}
				LinearInequality li =
						sig.generate(m_stem_transition.getOutVars());
				li.negate();
				motzkin.add_inequality(li);
				conj.add(motzkin.transform());
			}
			// si(x) /\ loop(x, x') -> si(x')
			for (List<LinearInequality> loopConj : m_loop) {
				MotzkinTransformation motzkin =
						new MotzkinTransformation(m_script);
				for (LinearInequality li : loopConj) {
					motzkin.add_inequality(li);
				}
				motzkin.add_inequality(sig.generate(
						m_loop_transition.getInVars())); // si(x)
				LinearInequality li = sig.generate(
						m_loop_transition.getOutVars()); // ~si(x')
				li.needs_motzkin_coefficient =
						!Preferences.nondecreasing_invariants;
				li.negate();
				motzkin.add_inequality(li);
				conj.add(motzkin.transform());
			}
		}
		return conj;
	}
	
	private Map<Term, Rational> preprocessValuation(Map<Term, Term> val)
			throws TermException {
		Map<Term, Rational> new_val = new HashMap<Term, Rational>();
		for (Entry<Term, Term> entry : val.entrySet()) {
			new_val.put(entry.getKey(),
					AuxiliaryMethods.const2Rational(entry.getValue()));
		}
		return new_val;
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
	 * @param TemplateClass the class of the ranking template to be used
	 * @return whether a ranking function was found
	 * @throws SMTLIBException in case of trouble with the theorem prover
	 * @throws TermIsNotAffineException if the supplied transitions contain
	 *          non-affine update statements
	 * @throws InstantiationException if something went wrong during
	 *          instantiation of the template class
	 */
	/**
	 * 
	 * @param template
	 * @return
	 * @throws SMTLIBException
	 * @throws TermException
	 */
	public boolean synthesize(RankingFunctionTemplate template)
			throws SMTLIBException, TermException {
		checkPreferences();
		
		template.init(m_script, getRankVars());
		
		// Check if the loop transition is trivial
		if (m_loop_transition.getFormula() instanceof ApplicationTerm) {
			ApplicationTerm loopf = (ApplicationTerm)
					m_loop_transition.getFormula();
			if (loopf.getFunction().getName() == "false") {
				s_Logger.info("Loop transition is equivalent to false.");
//				m_ranking_function = new LinearRankingFunction();
				return true;
			}
			if (loopf.getFunction().getName() == "true") {
				s_Logger.info("Loop transition is equivalent to true.");
				return false;
			}
		}
		
		s_Logger.info("Using template '" + template.getClass().getSimpleName()
				+ "'.");
		s_Logger.debug("Template formula:\n" + template);
		
		// List of all used supporting invariant generators
		Collection<SupportingInvariantGenerator> si_generators =
				new ArrayList<SupportingInvariantGenerator>();
		
		// Assert all conjuncts generated from the template
		Collection<Term> conj = buildConstraints(template, si_generators);
		
		StringBuilder sb = new StringBuilder();
		sb.append("The template built the following SMT formulae:\n");
		for (Term t : conj) {
			if (t instanceof ApplicationTerm
					&& ((ApplicationTerm) t).getFunction().getName() == "and") {
				ApplicationTerm appt = (ApplicationTerm) t;
				for (Term t2 : appt.getParameters()) {
					sb.append(t2);
					sb.append("\n");
				}
			} else {
				sb.append(t);
				sb.append("\n");
			}
			m_script.assertTerm(t);
		}
		s_Logger.debug(sb.toString());
		
		// Check for a model
		if (m_script.checkSat() == LBool.SAT) {
			s_Logger.debug("Found a model, " +
					"proceeding to extract ranking function.");
			
			// Extract ranking function
			Map<Term, Rational> val_rf = preprocessValuation(m_script.getValue(
					template.getVariables().toArray(new Term[0])));
			m_ranking_function = template.extractRankingFunction(val_rf);
			
			// Extract supporting invariants
			for (SupportingInvariantGenerator sig : si_generators) {
				Map<Term, Rational> val_si = preprocessValuation(m_script.getValue(
						sig.getVariables().toArray(new Term[0])));
				m_supporting_invariants.add(sig.extractSupportingInvariant(
						val_si));
			}
			return true;
		}
		return false;
	}
	
	/**
	 * Return the generated ranking function.
	 * Call after synthesize().
	 */
	public RankingFunction getRankingFunction() {
		return m_ranking_function;
	}
	
	/**
	 * Return the generated supporting invariant.
	 * Call after synthesize().
	 */
	public Collection<SupportingInvariant> getSupportingInvariants() {
		return m_supporting_invariants;
	}
}
