package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;

import java.util.*;
import java.lang.reflect.InvocationTargetException;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.Preferences.UseDivision;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.*;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.templates.RankingTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;


/**
 * This is a synthesizer for generating linear ranking functions simple lasso
 * programs.
 * 
 * @author Jan Leike
 */
public class RankingFunctionsSynthesizer {
	
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
	
	// Stem and loop transitions for the lasso program
	private TransFormula m_stem;
	private TransFormula m_loop;
	
	// Transition formulae in DNF
	private Collection<Term> m_stem_clauses;
	private Collection<Term> m_loop_clauses;
	
	// Objects resulting from the synthesis process
	private RankingFunction m_ranking_function = null;
	private Collection<SupportingInvariant> m_supporting_invariants = null;
	
	private int m_auxNameIndex;
	
	private Collection<TermVariable> m_auxVars;
	
	/**
	 * Reals or Integers?
	 */
	public enum VariableDomain {
		REALS,
		INTEGERS
	}
	
	/**
	 * Is the program over real valued or over integer variables?
	 */
	public VariableDomain m_variable_domain;
	
	/**
	 * Constructor for the ranking function synthesizer.
	 * @param stem transition formula for the program's stem
	 * @param loop transition formula for the program's loop
	 * @param script SMT Solver
	 * @throws Exception If something goes wrong ;)
	 */
	public RankingFunctionsSynthesizer(Script old_script, Script script,
			TransFormula stem, TransFormula loop) throws Exception {
		m_old_script = old_script;
		m_script = script;
		
		m_stem = stem;
		m_loop = loop;
		
		m_auxVars = new ArrayList<TermVariable>();
		m_supporting_invariants = new ArrayList<SupportingInvariant>();
		
		Term stem_term = stem.getFormula();
		Term loop_term = loop.getFormula();
		
		if (Preferences.use_division == UseDivision.C_STYLE) {
			// Replace integer division
			int i = findMinAuxName(stem.getFormula());
			int j = findMinAuxName(loop.getFormula());
			m_auxNameIndex = i > j ? i : j;
			stem_term = replaceDiv(stem_term);
			loop_term = replaceDiv(loop_term);
		}
		
		// Replace !=
		stem_term = replaceNeq(stem_term);
		loop_term = replaceNeq(loop_term);
		
		// Convert to DNF
		m_stem_clauses = AuxiliaryMethods.toDNF(m_old_script, stem_term);
		m_loop_clauses = AuxiliaryMethods.toDNF(m_old_script, loop_term);
		
		if (!Preferences.enable_disjunction &&
				(m_stem_clauses.size() > 1 || m_loop_clauses.size() > 1)) {
			throw new Exception("Support for disjunctions in stem and loop " +
					"transitions is disabled.");
		}
		
		// Display some debug info
		s_Logger.debug("Constructed the sythesizer.");
		s_Logger.debug("Stem transition: " + m_stem);
		s_Logger.debug("Loop transition: " + m_loop);
		
		// Set variable domain
		switch (Preferences.use_variable_domain) {
		case AUTO_DETECT:
			m_variable_domain = deriveVariableDomain();
			break;
		case INTEGERS:
			m_variable_domain = VariableDomain.INTEGERS;
			break;
		case REALS:
			m_variable_domain = VariableDomain.REALS;
			break;
		default:
			throw new Exception("Unknown variable domain");
		}
		s_Logger.info("Using variable domain " + m_variable_domain + ".");
	}
	
	/**
	 * Try to automatically derive a variable domain.
	 * The variable domain is Integer if all variables are of Sort 'Int',
	 * and Real otherwise.
	 */
	private VariableDomain deriveVariableDomain() {
		VariableDomain domain = VariableDomain.INTEGERS;
		
		// Check the stem variables
		for (TermVariable var : m_stem.getInVars().values()) {
			if (var.getSort().getName() != "Int") {
				domain = VariableDomain.REALS;
				break;
			}
		}
		for (TermVariable var : m_stem.getOutVars().values()) {
			if (var.getSort().getName() != "Int") {
				domain = VariableDomain.REALS;
				break;
			}
		}
		for (TermVariable var : m_stem.getAuxVars()) {
			if (var.getSort().getName() != "Int") {
				domain = VariableDomain.REALS;
				break;
			}
		}
		
		// Check the loop variables
		for (TermVariable var : m_loop.getInVars().values()) {
			if (var.getSort().getName() != "Int") {
				domain = VariableDomain.REALS;
				break;
			}
		}
		for (TermVariable var : m_loop.getOutVars().values()) {
			if (var.getSort().getName() != "Int") {
				domain = VariableDomain.REALS;
				break;
			}
		}
		for (TermVariable var : m_loop.getAuxVars()) {
			if (var.getSort().getName() != "Int") {
				domain = VariableDomain.REALS;
				break;
			}
		}
		
		return domain;
	}
	
	/**
	 * Replace every occurrence of "x != y" with "x < y or x > y".
	 * @param t term
	 * @return the same term with the replaced instances
	 */
	private Term replaceNeq(Term t) {
		// replaceNeq operates on the transition formula, therefore uses
		// m_old_script
		// TODO: use TermTransformer?
		if (!(t instanceof ApplicationTerm)) {
			return t;
		}
		ApplicationTerm appt = (ApplicationTerm) t;
		String func = appt.getFunction().getName();
		if (func == "not") {
			assert(appt.getParameters().length == 1);
			Term t2 = appt.getParameters()[0];
			if (!(t2 instanceof ApplicationTerm)) {
				return t;
			}
			ApplicationTerm appt2 = (ApplicationTerm) t2;
			String func2 = appt2.getFunction().getName();
			if (func2 == "=") {
				assert(appt2.getParameters().length == 2);
				Term param1 = m_old_script.term("<", appt2.getParameters());
				Term param2 = m_old_script.term(">", appt2.getParameters());
				return m_old_script.term("or", param1, param2);
			}
			
			return m_old_script.term("not", replaceNeq(t2));
		}
		// Else proceed recursively
		Collection<Term> parameters = new ArrayList<Term>();
		for (Term param : appt.getParameters()) {
			parameters.add(replaceNeq(param));
		}
		return m_old_script.term(func, parameters.toArray(new Term[0]));
	}
	
	/**
	 * Recursively find the largest i such that s_auxPrefix + i is a used
	 * variable.
	 * @param t term
	 * @return i
	 */
	private int findMinAuxName(Term t) {
		if (!(t instanceof ApplicationTerm)) {
			return 0;
		}
		ApplicationTerm appt = (ApplicationTerm) t;
		String func = appt.getFunction().getName();
		if (func.startsWith(s_auxPrefix)) {
			try {
				String num = func.substring(s_auxPrefix.length());
				int n = Integer.parseInt(num);
				return n;
			} catch (NumberFormatException e) {
				// Do nothing
			}
		}
		// Proceed recursively
		int i = 0;
		for (Term param : appt.getParameters()) {
			int n = findMinAuxName(param);
			i = n > i ? n : i;
		}
		return i;
	}
	
	/**
	 * Replace integer division by equivalent linear constraints
	 * @param t term
	 * @return replaced term
	 */
	private Term replaceDiv(Term t) {
		List<Term> auxTerms = new ArrayList<Term>();
		Term t2 = replaceDivRec(t, auxTerms);
		for (Term term : auxTerms) {
			t2 = m_old_script.term("and", t2, term);
		}
		return t2;
	}
	
	/**
	 * Replace every occurrence of "div x y" with
	 * (x < 0 \/ (y*z <= x /\ x < (y + 1)*z)) /\
	 * (x >= 0 \/ ((y + 1)*z < x /\ x <= y*z))
	 * Introduces new auxiliary variables.
	 * Does not check if things are linear.
	 * @param t term
	 * @param collector for the constraints to the auxiliary variables
	 * @return the same term with the replaced instances
	 */
	private Term replaceDivRec(Term t, List<Term> auxTerms) {
		// replaceDiv operates on the transition formula, therefore uses
		// m_old_script
		// TODO: use TermTransformer?
		if (!(t instanceof ApplicationTerm)) {
			return t;
		}
		ApplicationTerm appt = (ApplicationTerm) t;
		String func = appt.getFunction().getName();
		if (func == "div") {
			assert(appt.getParameters().length == 2);
			Term divident = replaceDivRec(appt.getParameters()[0], auxTerms);
			Term divisor  = replaceDivRec(appt.getParameters()[1], auxTerms);
			String name = s_auxPrefix + m_auxNameIndex;
			m_auxNameIndex++;
			Term auxVar = m_old_script.variable(name, m_old_script.sort("Int"));
			m_auxVars.add((TermVariable) auxVar);
			// x < 0 \/ (y*z <= x /\ x < (y + 1)*z)
			Term conj1 = m_old_script.term("and",
					m_old_script.term("<=", m_old_script.term("*",
							divident, divisor), auxVar),
					m_old_script.term("<", auxVar, m_old_script.term("*",
							divident, m_old_script.term("+", divisor,
									m_old_script.numeral(BigInteger.ONE)))));
			auxTerms.add(m_old_script.term("or",
					m_old_script.term("<", divident,
							m_old_script.numeral(BigInteger.ZERO)), conj1));
			// x >= 0 \/ ((y + 1)*z < x /\ x <= y*z)
			Term conj2 = m_old_script.term("and",
					m_old_script.term("<", m_old_script.term("*",
							divident, m_old_script.term("+", divisor,
							m_old_script.numeral(BigInteger.ONE))), auxVar),
					m_old_script.term("<=", auxVar,  m_old_script.term("*",
									divident, divisor)));
			auxTerms.add(m_old_script.term("or",
					m_old_script.term(">=", divident,
							m_old_script.numeral(BigInteger.ZERO)), conj2));
			return auxVar;
		}
		// Else proceed recursively
		Collection<Term> parameters = new ArrayList<Term>();
		for (Term param : appt.getParameters()) {
			parameters.add(replaceDivRec(param, auxTerms));
		}
		return m_old_script.term(func, parameters.toArray(new Term[0]));
	}
	
	/**
	 * Convert an (in-)equality into affine term(s) of the form
	 * Σ c_i x_i + c <= 0
	 * where the non-positivity is implicit.
	 * @param term
	 * @param list a list of affine terms where the new terms should be
	 *              inserted 
	 * @throws TermIsNotAffineException iff the input term cannot be reduced to
	 *          an affine term 
	 */
	private void convertIE(ApplicationTerm term,
			Collection<AffineTerm> list) throws TermIsNotAffineException {
		ApplicationTerm appt = (ApplicationTerm) term;
		if (appt.getParameters().length != 2) {
			throw new TermIsNotAffineException(
					"Unsupported number of parameters", appt);
		}
		String fname = appt.getFunction().getName();
		AffineTerm at1 = AffineTerm.fromTerm(appt.getParameters()[0],
				m_variable_domain);
		AffineTerm at2 = AffineTerm.fromTerm(appt.getParameters()[1],
				m_variable_domain);
		AffineTerm res;
		if (fname == "<=") {
			at2.mult(Rational.MONE);
			res = at1;
			res.add(at2);
		} else if (fname == ">=") {
			at1.mult(Rational.MONE);
			res = at1;
			res.add(at2);
		} else if (fname == "=") {
			at2.mult(Rational.MONE);
			at1.add(at2);
			res = new AffineTerm();
			res.add(at1);
			res.mult(Rational.MONE);
			list.add(res);
			res = at1;
		} else if (fname == "<") {
			at2.mult(Rational.MONE);
			res = at1;
			res.add(at2);
			if (this.m_variable_domain == VariableDomain.INTEGERS) {
				res.add(Rational.ONE);
			}
		} else if (fname == ">") {
			res = at1;
			res.mult(Rational.MONE);
			res.add(at2);
			if (this.m_variable_domain == VariableDomain.INTEGERS) {
				res.add(Rational.ONE);
			}
			// Over Reals is the method complete even if strict inequalities
			// are replaced by non-strict inequalities.
		} else {
			throw new TermIsNotAffineException("Expected an (in-)equality.",
					appt);
		}
		list.add(res);
	}
	
	/**
	 * For a polyhedron given by a collection of affine terms, return the
	 * integral hull, i.e. the convex hull of all integral points contained
	 * in the polyhedron.
	 * The returned list of affine terms contains all of the supplied affine
	 * terms.
	 */
	private List<AffineTerm> integralHull(Collection<AffineTerm> polyh) {
		List<AffineTerm> ipolyh = new ArrayList<AffineTerm>();
		ipolyh.addAll(polyh);
		
		// TODO
		s_Logger.error("Computation of the intregral hull is not yet "
				+ "implemented; continuing with the original constraints.");
		
		assert(ipolyh.containsAll(polyh));
		return ipolyh;
	}
	
	/**
	 * Generate a list of affine terms form a transition formula.
	 * @param t term of the transition formula
	 * @return list of affine terms
	 * @throws TermIsNotAffineException if the supplied (in-)equalities in the
	 *          transition formula are not affine
	 */
	private List<AffineTerm> generateAffineTerms(Term term)
			throws TermIsNotAffineException {
		List<AffineTerm> terms = new ArrayList<AffineTerm>();
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			String fname = appt.getFunction().getName();
			if (fname == "and") {
				for (Term t : appt.getParameters()) {
					terms.addAll(generateAffineTerms(t));
				}
			} else if (fname == "true") {
				// Add nothing
			} else if (fname == "=")  {
				Term param0 = appt.getParameters()[0];
				Sort param0sort = param0.getSort();
				if (param0sort.isNumericSort()) {
					convertIE(appt, terms);
				} else if (param0sort.getName().equals("Bool")) {
					s_Logger.warn("ignoring term: " + term);
				} else {
					throw new TermIsNotAffineException(
							"Unknown sort in equality", appt);
				}
			} else if (fname == "<" || fname == ">"
					|| fname == "<=" || fname == ">=") {
				convertIE(appt, terms);
			} else {
				throw new TermIsNotAffineException(
						"Unfamiliar application term.", appt);
			}
		} else if (term instanceof TermVariable)
			s_Logger.warn("Ignored boolean TermVariable " + term);
		else {
			throw new TermIsNotAffineException("Expected application term.",
					term);
		}
		return terms;
	}
	
	/**
	 * Create a template instance for the given template class
	 * @param TemplateClass Subclass of RankingTemplate to be instantiated
	 * @param transVars Collection of BoogieVars used for ranking
	 * @return Template instance
	 * @throws InstantiationException if instantiation failed somehow
	 */
	private RankingTemplate instantiateTemplate(
			Class<? extends RankingTemplate> TemplateClass,
			Collection<BoogieVar> transVars)
					throws InstantiationException {
		RankingTemplate template;
		try {
			template = (RankingTemplate)
					TemplateClass.getConstructors()[0].newInstance(m_script,
							transVars);
		} catch (InvocationTargetException ex) {
			throw new InstantiationException(); // Redirect
		} catch (IllegalAccessException ex) {
			throw new InstantiationException(); // Redirect
		}
		return template;
	}
	
	/**
	 * Use the ranking template to build a formula for the theorem prover
	 * @param template The template to be used
	 * @param si_generators To this add used si generators will be added
	 * @param stem_terms List of conjuncts in the stem transition formula
	 * @param loop_terms List of conjuncts in the loop transition formula
	 * @param transTVars Collection of TermVariables used in the transition
	 * @return List of all conjuncts of the formula
	 */
	private Collection<Term> buildFromTemplate(RankingTemplate template,
			Collection<SupportingInvariantGenerator> si_generators,
			List<List<AffineTerm>> stem_terms,
			List<List<AffineTerm>> loop_terms) {
		// List of conjuncts for the theorem prover
		List<Term> conj = new ArrayList<Term>();
		
		// All variables relevant for supporting invariants
		// Variables that are not read by the loop are not relevant for 
		// supporting invariants.
		Collection<BoogieVar> siVars = new HashSet<BoogieVar>(); 
		siVars = m_stem.getOutVars().keySet();
//		siVars.retainAll(m_loop.getInVars().keySet());
		
		// Collect all loop variables
		Collection<TermVariable> loop_vars = new HashSet<TermVariable>();
		loop_vars.addAll(m_loop.getInVars().values());
		loop_vars.addAll(m_loop.getOutVars().values());
		loop_vars.addAll(m_auxVars);
		
		// Farkas' Lemma applications, iterate over the loop disjunction
		for (List<AffineTerm> loop_conj : loop_terms) {
			
			Collection<Term> loop_impossible = new ArrayList<Term>();
				// List of conjuncts for the case where loop execution is
				// impossible
			Collection<Term> loop_possible = new ArrayList<Term>();
				// List of conjuncts for the case where loop execution is
				// possible
			
			Collection<Collection<FarkasApplication>> farkasCNF =
					template.generateFarkas(m_loop.getInVars(),
							m_loop.getOutVars());
			
			for (Collection<FarkasApplication> farkasClause : farkasCNF) {
				SupportingInvariantGenerator sig = null;
				Collection<Term> disj = new ArrayList<Term>();
				for (FarkasApplication farkas : farkasClause) {
					if (Preferences.add_supporting_invariants && farkas.wantsSI) {
						if (sig == null) {
							sig = new SupportingInvariantGenerator(m_script,
									siVars);
							si_generators.add(sig);
						}
						sig.addSI(farkas, m_loop.getInVars());
					}
					farkas.terms = loop_conj;
					farkas.transitionVariables = loop_vars;
					disj.add(m_script.term("and",
							farkas.transform().toArray(new Term[0])));
				}
				if (disj.size() > 1) {
					loop_possible.add(m_script.term("or",
							disj.toArray(new Term[0])));
				} else {
					loop_possible.addAll(disj);
				}
			}
			
			if (Preferences.check_if_loop_impossible) {
				// loop(x, x') -> si(x) < 0 (loop will never execute)
				FarkasApplication loop_imp = new FarkasApplication(m_script);
				loop_imp.terms = loop_conj;
				loop_imp.transitionVariables = loop_vars;
				loop_imp.ieqsymb = FarkasApplication.Inequality.LESS_THAN;
				SupportingInvariantGenerator sig =
						new SupportingInvariantGenerator(m_script, siVars);
				si_generators.add(sig);
				sig.addSI(loop_imp, m_loop.getInVars());
				loop_impossible.addAll(loop_imp.transform());
				
				// Loop iteration impossible or ranking function properties hold
				conj.add(m_script.term("or",
					m_script.term("and", loop_possible.toArray(new Term[0])),
					m_script.term("and", loop_impossible.toArray(new Term[0]))
				));
			} else {
				conj.addAll(loop_possible);
			}
		}
		
		if (Preferences.add_supporting_invariants) {
			// Take care of the supporting invariants
			for (SupportingInvariantGenerator sig : si_generators) {
				for (List<AffineTerm> stem_conj : stem_terms) {
					// stem(x, x0) -> si(x0) >= 0
					FarkasApplication stem0 = new FarkasApplication(m_script);
					stem0.terms = stem_conj;
					stem0.transitionVariables = new HashSet<TermVariable>();
					stem0.transitionVariables.addAll(m_stem.getInVars().values());
					stem0.transitionVariables.addAll(m_stem.getOutVars().values());
					stem0.transitionVariables.addAll(m_auxVars);
					stem0.ieqsymb =
							FarkasApplication.Inequality.LESS_THAN_OR_EQUAL;
					// consider only vars that occur as inVars of loop
					Map<BoogieVar, TermVariable> relevantOutVars = new HashMap<BoogieVar, TermVariable>();
					for (BoogieVar bv : m_loop.getInVars().keySet()) {
						if (m_stem.getOutVars().containsKey(bv))  {
							relevantOutVars.put(bv, m_stem.getOutVars().get(bv));
						}
					}
					sig.setStemEntailment(stem0, relevantOutVars);
					conj.addAll(stem0.transform());
				}
				for (List<AffineTerm> loop_conj : loop_terms) {
					// loop(x, x') -> si(x') >= si(x)
					FarkasApplication nondecr = new FarkasApplication(m_script);
					nondecr.terms = loop_conj;
					nondecr.transitionVariables = loop_vars;
					nondecr.ieqsymb =
							FarkasApplication.Inequality.LESS_THAN_OR_EQUAL;
					Map<BoogieVar, TermVariable> relevantInVars = new HashMap<BoogieVar, TermVariable>();
					for (BoogieVar bv : m_loop.getInVars().keySet()) {
						if (m_stem.getOutVars().containsKey(bv))  {
							relevantInVars.put(bv, m_loop.getInVars().get(bv));
						}
					}
					sig.setSINonDecreasing(nondecr, relevantInVars,
							m_loop.getOutVars());
					conj.addAll(nondecr.transform());
				}
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
	 * @param TemplateClass the class of the ranking template to be used
	 * @return whether a ranking function was found
	 * @throws SMTLIBException in case of trouble with the theorem prover
	 * @throws TermIsNotAffineException if the supplied transitions contain
	 *          non-affine update statements
	 * @throws InstantiationException if something went wrong during
	 *          instantiation of the template class
	 */
	public boolean synthesize(Class<? extends RankingTemplate> TemplateClass)
			throws SMTLIBException, TermIsNotAffineException,
			InstantiationException {
		s_Logger.debug("Current Preferences:\n" + Preferences.show());
		if (!Preferences.add_supporting_invariants) {
			s_Logger.warn("Generation of supporting invariants is disabled.");
		}
		if (!Preferences.check_if_loop_impossible) {
			s_Logger.warn("Check for loop impossibility is disabled.");
		}
		if (Preferences.use_division == UseDivision.C_STYLE
				&& !Preferences.enable_disjunction) {
			s_Logger.warn("Using C-style integer division, but support for " +
				"disjunctions is disabled.");
		}
		
		// Check if the loop transition is trivial
		if (m_loop.getFormula() instanceof ApplicationTerm) {
			ApplicationTerm loopf = (ApplicationTerm) m_loop.getFormula();
			if (loopf.getFunction().getName() == "false") {
				s_Logger.warn("Loop transition is equivalent to false.");
				m_ranking_function = new LinearRankingFunction();
				return true;
			}
			if (loopf.getFunction().getName() == "true") {
				s_Logger.warn("Loop transition is equivalent to true.");
				return false;
			}
		}
		
		// Transform the stem and loop transition into affine terms
		List<List<AffineTerm>> stem_terms = new ArrayList<List<AffineTerm>>();
		for (Term clause : m_stem_clauses) {
			List<AffineTerm> at = generateAffineTerms(clause);
			if (this.m_variable_domain == VariableDomain.INTEGERS
					&& Preferences.compute_integral_hull) {
				at = this.integralHull(at);
			}
			stem_terms.add(at);
		}
		List<List<AffineTerm>> loop_terms = new ArrayList<List<AffineTerm>>();
		for (Term clause : m_loop_clauses) {
			List<AffineTerm> at = generateAffineTerms(clause);
			if (this.m_variable_domain == VariableDomain.INTEGERS
					&& Preferences.compute_integral_hull) {
				at = this.integralHull(at);
			}
			loop_terms.add(at);
		}
		
		s_Logger.debug("Stem terms:\n" + stem_terms);
		s_Logger.debug("Loop terms:\n" + loop_terms);
		
		// rankVars = all Boogie variables relevant to the ranking function
		Collection<BoogieVar> rankVars = new HashSet<BoogieVar>();
		rankVars.addAll(m_loop.getOutVars().keySet());
		rankVars.retainAll(m_loop.getInVars().keySet());
		
		// Create a template instance
		RankingTemplate template = instantiateTemplate(TemplateClass, rankVars);
		s_Logger.info("Using template \"" + TemplateClass.getSimpleName()
				+ "\".");
		s_Logger.debug("Template formula:\n" + template);
		s_Logger.debug("Generated instance:\n"
				+ template.getDetails(m_loop.getInVars(), m_loop.getOutVars()));
		
		// List of all used supporting invariant generators
		Collection<SupportingInvariantGenerator> si_generators =
				new ArrayList<SupportingInvariantGenerator>();
		
		// Assert all conjuncts generated from the template
		Collection<Term> conj = buildFromTemplate(template, si_generators,
				stem_terms, loop_terms);
		s_Logger.debug("The template built the following SMT formulae:");
		for (Term t : conj) {
			if (t instanceof ApplicationTerm
					&& ((ApplicationTerm) t).getFunction().getName() == "and") {
				ApplicationTerm appt = (ApplicationTerm) t;
				for (Term t2 : appt.getParameters()) {
					s_Logger.debug(t2);
				}
			} else {
				s_Logger.debug(t);
//				s_Logger.debug(SMTTermPrinter.print(t));
			}
			m_script.assertTerm(t);
		}
		
		// Check for a model
		boolean success = m_script.checkSat() == LBool.SAT;
		if (success) {
			s_Logger.debug("Found a model, " +
					"proceeding to extract ranking function.");
			
			// Extract ranking function
			Valuation val_rf = m_script.getValue(
					template.getVariables().toArray(new Term[0]));
			m_ranking_function = template.extractRankingFunction(val_rf);
			
			// Extract supporting invariants
			for (SupportingInvariantGenerator sig : si_generators) {
				Valuation val_si = m_script.getValue(
						sig.getVariables().toArray(new Term[0]));
				m_supporting_invariants.add(sig.extractSupportingInvariant(
						val_si));
			}
		}
		
		return success;
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
