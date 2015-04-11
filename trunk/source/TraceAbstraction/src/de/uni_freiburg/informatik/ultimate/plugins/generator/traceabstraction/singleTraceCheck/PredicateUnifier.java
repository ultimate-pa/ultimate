package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.CheckClosedTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineSubtermNormalizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;

/**
 * Data structure that stores for each term a unique predicate. 
 * Initially a predicate unifier constructs a "true" predicate and a "false" 
 * predicate.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class PredicateUnifier {

	private final SmtManager m_SmtManager;
	private final Map<Term, IPredicate> m_Term2Predicates;
	private final List<IPredicate> m_KnownPredicates = new ArrayList<IPredicate>();
	private final CoverageRelation m_CoverageRelation = new CoverageRelation();
	private boolean m_BringTermsToPositiveNormalForm = true;
	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	
	private final IPredicate m_TruePredicate;
	private final IPredicate m_FalsePredicate;

	public PredicateUnifier(IUltimateServiceProvider services, SmtManager smtManager, IPredicate... initialPredicates) {
		m_SmtManager = smtManager;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Term2Predicates = new HashMap<Term, IPredicate>();
		Term trueTerm = m_SmtManager.getScript().term("true");
		IPredicate truePredicate = null;
		Term falseTerm = m_SmtManager.getScript().term("false");
		IPredicate falsePredicate = null;
		for (IPredicate pred : initialPredicates) {
			if (pred.getFormula().equals(trueTerm)) {
				truePredicate = pred;
			} else if (pred.getFormula().equals(falseTerm)) {
				falsePredicate = pred;
			}
		}
		if (truePredicate == null) {
			m_TruePredicate = m_SmtManager.newTruePredicate();
		} else {
			m_TruePredicate = truePredicate;
		}
		if (falsePredicate == null) {
			m_FalsePredicate = m_SmtManager.newFalsePredicate();
		} else {
			m_FalsePredicate = falsePredicate;
		}
		declareTruePredicateAndFalsePredicate();
		for (IPredicate pred : initialPredicates) {
			declarePredicate(pred);
		}
	}
	
	public IPredicate getTruePredicate() {
		return m_TruePredicate;
	}

	public IPredicate getFalsePredicate() {
		return m_FalsePredicate;
	}
	
	private void declareTruePredicateAndFalsePredicate() {
		Map<IPredicate, Validity> impliedByTrue = Collections.emptyMap();
		Map<IPredicate, Validity> expliedByTrue = Collections.emptyMap();
		addNewPredicate(m_TruePredicate, m_TruePredicate.getFormula(), 
				m_TruePredicate.getFormula(), impliedByTrue, expliedByTrue);
		Map<IPredicate, Validity> impliedByFalse = 
				Collections.singletonMap(m_TruePredicate, Validity.VALID);
		Map<IPredicate, Validity> expliedByFalse = 
				Collections.singletonMap(m_TruePredicate, Validity.INVALID);
		addNewPredicate(m_FalsePredicate, m_FalsePredicate.getFormula(),
				m_FalsePredicate.getFormula(), impliedByFalse, expliedByFalse);
	}


	/**
	 * Return true iff pred is the representative IPredicate for the Term
	 * pred.getFormula().
	 */
	boolean isRepresentative(IPredicate pred) {
		IPredicate representative = m_Term2Predicates.get(pred.getFormula());
		return pred == representative;
	}

	/**
	 * Add predicate. Store this predicate without further simplification. Throw
	 * an exception if this PredicateUnifier stores already an equivalent
	 * predicate.
	 */
	void declarePredicate(IPredicate predicate) {
		PredicateComparison pc = new PredicateComparison(predicate.getFormula(), predicate.getVars());
		if (pc.isEquivalentToExistingPredicate()) {
			if (pc.getEquivalantPredicate() != predicate) {
				throw new AssertionError("There is already an" + " equivalent predicate");
			}
		} else {
			addNewPredicate(predicate, predicate.getFormula(), predicate.getFormula(), 
					pc.getImpliedPredicates(), pc.getExpliedPredicates());
		}
	}

	public IPredicate getOrConstructPredicate(TermVarsProc tvp) {
		return getOrConstructPredicate(tvp.getFormula(), tvp.getVars(), tvp.getProcedures());
	}

	/**
	 * Returns true iff each free variables corresponds to a BoogieVar in vars.
	 * Throws an Exception otherwise.
	 */
	private boolean varsIsSupersetOfFreeTermVariables(Term term, Set<BoogieVar> vars) {
		for (TermVariable tv : term.getFreeVars()) {
			BoogieVar bv = m_SmtManager.getBoogie2Smt().getBoogie2SmtSymbolTable().getBoogieVar(tv);
			if (bv == null) {
				throw new AssertionError("Variable " + tv + " has no corresponding BoogieVar, hence seems "
						+ "to be some auxiliary variable and may not "
						+ "occur unquantified in the formula of a predicate");
			} else {
				if (!vars.contains(bv)) {
					throw new AssertionError("Variable " + tv + " does not occur in vars");
				}
			}
		}
		return true;
	}

	/**
	 * Get the predicate for term. If there is not yet a predicate for term,
	 * construct the predicate using vars.
	 * 
	 * @param vars
	 *            The BoogieVars of the TermVariables contained in term.
	 * @param proc
	 *            All procedures of which vars contains local variables.
	 */
	public IPredicate getOrConstructPredicate(Term term, Set<BoogieVar> vars, String[] procs) {
		assert varsIsSupersetOfFreeTermVariables(term, vars);
		if (term instanceof AnnotatedTerm) {
			AnnotatedTerm annotatedTerm = (AnnotatedTerm) term;
			Annotation[] annotations = annotatedTerm.getAnnotations();
			if (annotations.length == 1) {
				if (annotations[0].getKey().equals(":quoted")) {
					term = annotatedTerm.getSubterm();
				} else {
					throw new UnsupportedOperationException();
				}
			} else {
				throw new UnsupportedOperationException();
			}
		}

		IPredicate p = m_Term2Predicates.get(term);
		if (p != null) {
			return p;
		}
		
		PredicateComparison pc = new PredicateComparison(term, vars);
		if (pc.isEquivalentToExistingPredicate()) {
			return pc.getEquivalantPredicate();
		}
		final IPredicate result;
		assert !SmtUtils.isTrue(term) : "illegal predicate: true";
		assert !SmtUtils.isFalse(term) : "illegal predicate: false";
		assert !m_Term2Predicates.containsKey(term);
		Term simplifiedTerm = term;
		if (!pc.isIntricatePredicate()) {
			simplifiedTerm = SmtUtils.simplify(m_SmtManager.getScript(), term, mServices);
		}
		if (m_BringTermsToPositiveNormalForm) {
			simplifiedTerm = (new AffineSubtermNormalizer(m_SmtManager.getScript(), mLogger)).transform(term);
		}
		if (simplifiedTerm == term) {
			result = m_SmtManager.newPredicate(term, procs, vars, pc.getClosedTerm());
		} else {
			Set<TermVariable> tvs = new HashSet<TermVariable>(
					Arrays.asList(simplifiedTerm.getFreeVars()));
			Set<BoogieVar> newVars = new HashSet<BoogieVar>();
			Set<String> newProcs = new HashSet<String>();
			for (BoogieVar bv : vars) {
				if (tvs.contains(bv.getTermVariable())) {
					newVars.add(bv);
					if (bv.getProcedure() != null) {
						newProcs.add(bv.getProcedure());
					}
				}
			}
			Term closedTerm = PredicateUtils.computeClosedFormula(
					simplifiedTerm, vars, m_SmtManager.getScript());
			result = m_SmtManager.newPredicate(simplifiedTerm, 
					newProcs.toArray(new String[newProcs.size()]), 
					newVars, closedTerm);
		}
		addNewPredicate(result, term, simplifiedTerm, pc.getImpliedPredicates(), pc.getExpliedPredicates());
		assert new CheckClosedTerm().isClosed(result.getClosedFormula());
		assert varsIsSupersetOfFreeTermVariables(result.getFormula(), result.getVars());
		return result;
	}

	
	/**
	 * Add a new predicate. 
	 * @param pred
	 * @param simplifiedTerm 
	 * @param term 
	 * @param implied 
	 * 	Set of pairs (p,val) such that val is the validity of the implication pred ==> p.
	 * @param explied
	 *  Set of pairs (p,val) such that val is the validity of the explication pred <== p.
	 */
	private void addNewPredicate(IPredicate pred, Term term, Term simplifiedTerm, 
			Map<IPredicate, Validity> implied, Map<IPredicate, Validity> explied) {
		m_Term2Predicates.put(term, pred);
		m_Term2Predicates.put(simplifiedTerm, pred);
		m_CoverageRelation.addPredicate(pred, implied, explied);
		assert !m_KnownPredicates.contains(pred) : "predicate already known";
		m_KnownPredicates.add(pred);
	}


//	private IPredicate compareWithExistingPredicates(Term term, Set<BoogieVar> vars,
//			HashMap<IPredicate, Validity> impliedPredicats, HashMap<IPredicate, Validity> expliedPredicates) {
//		Term closedTerm = PredicateUtils.computeClosedFormula(term, vars, m_SmtManager.getScript());
//		assert impliedPredicats.isEmpty();
//		assert expliedPredicates.isEmpty();
//		m_SmtManager.lock(this);
//		m_SmtManager.getScript().echo(new QuotedObject("begin unification"));
//		for (Term interpolantTerm : m_Term2Predicates.keySet()) {
//			IPredicate interpolant = m_Term2Predicates.get(interpolantTerm);
//			Term interpolantClosedTerm = interpolant.getClosedFormula();
//			Validity implies = m_SmtManager.isCovered(this, closedTerm, interpolantClosedTerm);
//			impliedPredicats.put(interpolant, implies);
//			Validity explies = m_SmtManager.isCovered(this, interpolantClosedTerm, closedTerm);
//			expliedPredicates.put(interpolant, explies);
//			if (implies == Validity.VALID && explies == Validity.VALID) {
//				m_SmtManager.getScript().echo(new QuotedObject("end unification"));
//				m_SmtManager.unlock(this);
//				return interpolant;
//			}
//		}
//		m_SmtManager.getScript().echo(new QuotedObject("end unification"));
//		m_SmtManager.unlock(this);
//		return null;
//	}
	
	
	/**
	 * Compare Term term whose free variables represent the BoogieVars vars with
	 * all predicates that this Predicate unifier knows. If there exists a
	 * predicate for which we can prove that it is equivalent to term, this
	 * predicate is returned. Otherwise we return null and HashMaps
	 * impliedPredicats and expliedPredicates are filled with information about
	 * implications between term and existing Predicates.
	 * ImpliedPredicates will be filled with all IPredicates implied by term.
	 * ImpliedPredicates will be filled with all IPredicates that imply term.
	 * @return
	 */
	private class PredicateComparison {
		private final Term m_closedTerm;
		private final HashMap<IPredicate, Validity> impliedPredicates = new HashMap<IPredicate, Validity>();
		private final HashMap<IPredicate, Validity> expliedPredicates = new HashMap<IPredicate, Validity>();
		private final IPredicate m_EquivalantPredicate;
		private boolean m_IsIntricatePredicate;
		
		public Term getClosedTerm() {
			if (m_EquivalantPredicate != null) {
				throw new IllegalAccessError("not accessible, we found an equivalent predicate");
			}
			return m_closedTerm;
		}

		public HashMap<IPredicate, Validity> getImpliedPredicates() {
			if (m_EquivalantPredicate != null) {
				throw new IllegalAccessError("not accessible, we found an equivalent predicate");
			}

			return impliedPredicates;
		}

		public HashMap<IPredicate, Validity> getExpliedPredicates() {
			if (m_EquivalantPredicate != null) {
				throw new IllegalAccessError("not accessible, we found an equivalent predicate");
			}

			return expliedPredicates;
		}

		public IPredicate getEquivalantPredicate() {
			if (m_EquivalantPredicate == null) {
				throw new IllegalAccessError("accessible only if equivalent to existing predicate");
			}
			return m_EquivalantPredicate;
		}

		public boolean isIntricatePredicate() {
			if (m_EquivalantPredicate != null) {
				throw new IllegalAccessError("not accessible, we found an equivalent predicate");
			}

			return m_IsIntricatePredicate;
		}
		
		public boolean isEquivalentToExistingPredicate() {
			return m_EquivalantPredicate != null;
		}


		PredicateComparison(Term term, Set<BoogieVar> vars) {
			m_closedTerm = PredicateUtils.computeClosedFormula(term, vars, m_SmtManager.getScript());
			m_SmtManager.lock(this);
			m_SmtManager.getScript().echo(new QuotedObject("begin unification"));
			
			m_EquivalantPredicate = compare();

			m_SmtManager.getScript().echo(new QuotedObject("end unification"));
			m_SmtManager.unlock(this);
		}
		
		
		private IPredicate compare() {
			// check if false
			Validity impliesFalse = m_SmtManager.isCovered(this, m_closedTerm, m_FalsePredicate.getFormula());
			switch (impliesFalse) {
			case VALID:
				return m_FalsePredicate;
			case INVALID:
				impliedPredicates.put(m_FalsePredicate, Validity.INVALID);
				break;
			case UNKNOWN:
				mLogger.warn(new DebugMessage("unable to proof that {0} is different from false", m_closedTerm));
				impliedPredicates.put(m_FalsePredicate, Validity.UNKNOWN);
				m_IsIntricatePredicate = true;
				break;
			case NOT_CHECKED:
				throw new AssertionError("we wanted it checked");
			default:
				throw new AssertionError("unknown case");
			}
			// every predicate is implied by false
			expliedPredicates.put(m_FalsePredicate, Validity.VALID);
			
			// check if true
			Validity impliedByTrue = m_SmtManager.isCovered(this, m_TruePredicate.getClosedFormula(), m_closedTerm);
			switch (impliedByTrue) {
			case VALID:
				return m_TruePredicate;
			case INVALID:
				expliedPredicates.put(m_TruePredicate, Validity.INVALID);
				break;
			case UNKNOWN:
				mLogger.warn(new DebugMessage("unable to proof that {0} is different from true", m_closedTerm));
				expliedPredicates.put(m_TruePredicate, Validity.UNKNOWN);
				m_IsIntricatePredicate = true;
				break;
			case NOT_CHECKED:
				throw new AssertionError("we wanted it checked");
			default:
				throw new AssertionError("unknown case");
			}
			// every predicate implies true
			impliedPredicates.put(m_TruePredicate, Validity.VALID);
			
			// if predicate is intricate we do not compare against others
			if (m_IsIntricatePredicate) {
				for (IPredicate other : m_KnownPredicates) {
					if (other == m_TruePredicate || other == m_FalsePredicate) {
						continue;
					}
					impliedPredicates.put(other, Validity.NOT_CHECKED);
					expliedPredicates.put(other, Validity.NOT_CHECKED);
					continue;
				}
				return null;
			}
			
			for (IPredicate other : m_Term2Predicates.values()) {
				if (other == m_TruePredicate || other == m_FalsePredicate) {
					continue;
				}
				// we do not compare againts intricate predicates
				if (PredicateUnifier.this.isIntricatePredicate(other)) {
					impliedPredicates.put(other, Validity.NOT_CHECKED);
					expliedPredicates.put(other, Validity.NOT_CHECKED);
					continue;
				}
				Term otherClosedTerm = other.getClosedFormula();
				Validity implies = m_SmtManager.isCovered(this, m_closedTerm, otherClosedTerm);
				impliedPredicates.put(other, implies);
				Validity explies = m_SmtManager.isCovered(this, otherClosedTerm, m_closedTerm);
				expliedPredicates.put(other, explies);
				if (implies == Validity.VALID && explies == Validity.VALID) {
					return other;
				}
			}
			// no predicate was equivalent
			return null;
		}
	}
	
	

	/**
	 * We call a predicate "intricate" if we were unable to find our if it is
	 * equivalent to "true" or if we were unable to find out it it is equivalent
	 * to "false".
	 */
	public boolean isIntricatePredicate(IPredicate pred) {
		Validity equivalentToTrue = getCoverageRelation().isCovered(m_TruePredicate, pred);
		Validity equivalentToFalse = getCoverageRelation().isCovered(pred, m_FalsePredicate);
		if (equivalentToTrue == Validity.UNKNOWN || equivalentToFalse == Validity.UNKNOWN) {
			return true;
		} else {
			return false;
		}
	}


	/**
	 * Given a term "cut up" all its conjuncts. We bring the term in CNF and
	 * return an IPredicate for each conjunct.
	 */
	public Set<IPredicate> cannibalize(boolean splitNumericEqualities, Term term) {
		Set<IPredicate> result = new HashSet<IPredicate>();
		Term cnf = (new Cnf(m_SmtManager.getScript(), mServices, m_SmtManager.getVariableManager())).transform(term);
		Term[] conjuncts;
		if (splitNumericEqualities) {
			conjuncts = splitNumericEqualities(SmtUtils.getConjuncts(cnf));
		} else {
			conjuncts = SmtUtils.getConjuncts(cnf);
		}
		for (Term conjunct : conjuncts) {
			TermVarsProc tvp = TermVarsProc.computeTermVarsProc(conjunct, m_SmtManager.getBoogie2Smt());
			IPredicate predicate = getOrConstructPredicate(tvp);
			result.add(predicate);
		}
		return result;
	}

	private Term[] splitNumericEqualities(Term[] conjuncts) {
		ArrayList<Term> result = new ArrayList<>(conjuncts.length * 2);
		for (Term conjunct : conjuncts) {
			try {
				BinaryNumericRelation bnr = new BinaryNumericRelation(conjunct);
				if (bnr.getRelationSymbol() == RelationSymbol.EQ) {
					Term leq = m_SmtManager.getScript().term("<=", bnr.getLhs(), bnr.getRhs());
					result.add(leq);
					Term geq = m_SmtManager.getScript().term(">=", bnr.getLhs(), bnr.getRhs());
					result.add(geq);
				} else {
					result.add(conjunct);
				}
			} catch (NoRelationOfThisKindException e) {
				result.add(conjunct);
			}
		}
		return result.toArray(new Term[result.size()]);
	}

	public Set<IPredicate> cannibalizeAll(boolean splitNumericEqualities, IPredicate... predicates) {
		final Set<IPredicate> result = new HashSet<IPredicate>();
		for (IPredicate pred : predicates) {
			result.addAll(cannibalize(splitNumericEqualities, pred.getFormula()));
		}
		return result;
	}

	public IPredicateCoverageChecker getCoverageRelation() {
		return m_CoverageRelation;
	}

	public class CoverageRelation implements IPredicateCoverageChecker {

		NestedMap2<IPredicate, IPredicate, Validity> m_Lhs2RhsValidity = new NestedMap2<IPredicate, IPredicate, Validity>();
		HashRelation<IPredicate, IPredicate> m_ImpliedPredicates = new HashRelation<IPredicate, IPredicate>();
		HashRelation<IPredicate, IPredicate> m_ExpliedPredicates = new HashRelation<IPredicate, IPredicate>();
		
		void addPredicate(IPredicate pred, Map<IPredicate, Validity> implied, Map<IPredicate, Validity> explied) {
			assert !m_KnownPredicates.contains(pred) : "predicate already known";
			for (IPredicate known : m_KnownPredicates) {
				Validity implies = implied.get(known);
				Validity explies = explied.get(known);
				Validity oldimpl = m_Lhs2RhsValidity.put(pred, known, implies);
				assert oldimpl == null : "entry existed !";
				Validity oldexpl = m_Lhs2RhsValidity.put(known, pred, explies);
				assert oldexpl == null : "entry existed !";
				if (implies == Validity.VALID) {
					m_ImpliedPredicates.addPair(pred, known);
				}
				if (explies == Validity.VALID) {
					m_ImpliedPredicates.addPair(known, pred);
				}
			}
			m_ImpliedPredicates.addPair(pred, pred);
			m_ExpliedPredicates.addPair(pred, pred);
		}

		@Override
		public Validity isCovered(IPredicate lhs, IPredicate rhs) {
			if (lhs == rhs) {
				return Validity.VALID;
			}
			Validity result = m_Lhs2RhsValidity.get(lhs, rhs);
			if (result == null) {
				throw new AssertionError("at least one of both input predicates is unknown");
			}
			return result;
		}
		

		@Override
		public Set<IPredicate> getCoveringPredicates(IPredicate pred) {
			return Collections.unmodifiableSet(m_ImpliedPredicates.getImage(pred));
		}
		

		@Override
		public Set<IPredicate> getCoveredPredicates(IPredicate pred) {
			return Collections.unmodifiableSet(m_ExpliedPredicates.getImage(pred));
		}

	}
}