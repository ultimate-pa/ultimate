package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms.AffineSubtermNormalizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

	/**
	 * Data structure that stores for each term a unique predicate.
	 * @author heizmann@informatik.uni-freiburg.de
	 *
	 */
	public class PredicateUnifier {
		
		private final SmtManager m_SmtManager;
		private final Map<Term, IPredicate> m_Term2Predicates;
		private boolean m_BringTermsToPositiveNormalForm = true;
		
		public PredicateUnifier(SmtManager smtManager, IPredicate... initialPredicates) {
			m_SmtManager = smtManager;
			m_Term2Predicates = new HashMap<Term, IPredicate>();
			for (IPredicate pred : initialPredicates) {
				declarePredicate(pred);
			}
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
		 * Add the pair (predicate.getFormula(), predicate) to the 
		 * term2Predicate mapping if this pair is not already contained.
		 * Throw an exception if there is already a different predicate assigned
		 * to the term predicate.getFormula.  
		 */
		void declarePredicate(IPredicate predicate) {
			Term term = predicate.getFormula();
			IPredicate storedPredicate = m_Term2Predicates.get(term);
			if (storedPredicate == null) {
				m_Term2Predicates.put(term, predicate);
			} else {
				if (storedPredicate != predicate) {
					throw new AssertionError("There is already a" +
							" different predicate for this term");
				}
			}
		}
		
		/**
		 * Get the predicate for term. If there is not yet a predicate for term,
		 * construct the predicate using vars.
		 * @param vars The BoogieVars of the TermVariables contained in term.
		 * @param proc All procedures of which vars contains local variables.
		 */
		public IPredicate getOrConstructPredicate(Term term, Set<BoogieVar> vars, String[] procs) {
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
			ArrayList<IPredicate> impliedInterpolants = new ArrayList<IPredicate>();
			ArrayList<IPredicate> expliedInterpolants = new ArrayList<IPredicate>();
			p = getEquivalentPredicate(term, vars, 
									impliedInterpolants, expliedInterpolants);
			if (p != null) {
				return p;
			}  
			Term simplifiedTerm = m_SmtManager.simplify(term);
			if (simplifiedTerm == term) {
				//no simplification possible
				return addNewPredicate(term, vars, procs);
			} else {
				if (m_Term2Predicates.containsKey(simplifiedTerm)) {
					// this case can occur only if theorem prover says UNKNOWN
					// on equivalence checks
					return m_Term2Predicates.get(simplifiedTerm);
				}
				HashSet<TermVariable> tvs = new HashSet<TermVariable>();
				for (TermVariable tv : simplifiedTerm.getFreeVars()) {
					tvs.add(tv);
				}
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
				return addNewPredicate(simplifiedTerm, newVars, 
						newProcs.toArray(new String[0]));
			}

		}
		
		private IPredicate addNewPredicate(Term term, Set<BoogieVar> vars, 
															String[] procs) {
			assert !m_Term2Predicates.containsKey(term);
			IPredicate predicate;
			if (equivalentToTrue(term)) {
				Term trueTerm = m_SmtManager.getScript().term("true");
				predicate = m_Term2Predicates.get(trueTerm);
				if (predicate == null) {
					predicate = m_SmtManager.newTruePredicate();
				}
				TraceChecker.s_Logger.warn("Interpolant was equivalent to true");
			} else if (equivalentToFalse(term)){
				Term falseTerm = m_SmtManager.getScript().term("false");
				predicate = m_Term2Predicates.get(falseTerm);
				if (predicate == null) {
					predicate = m_SmtManager.newFalsePredicate();
				}
				TraceChecker.s_Logger.warn("Interpolant was equivalent to false");
			} else {
				if (m_BringTermsToPositiveNormalForm ) {
					term = (new AffineSubtermNormalizer(m_SmtManager.getScript())).transform(term);
				}
				Term closedTerm = SmtManager.computeClosedFormula(
										term, vars, m_SmtManager.getScript());
				predicate = m_SmtManager.newPredicate(
										term, procs, vars, closedTerm);
			}
			m_Term2Predicates.put(term, predicate);
			assert predicate != null;
			return predicate;
		}
		
		private IPredicate getEquivalentPredicate(Term term, Set<BoogieVar> vars,
				ArrayList<IPredicate> impliedInterpolants, ArrayList<IPredicate> expliedInterpolants) {
			Term closedTerm = SmtManager.computeClosedFormula(term, vars, m_SmtManager.getScript());
			for (Term interpolantTerm : m_Term2Predicates.keySet()) {
				IPredicate interpolant = m_Term2Predicates.get(interpolantTerm);
				Term interpolantClosedTerm = interpolant.getClosedFormula();
				LBool implies = m_SmtManager.isCovered(closedTerm, interpolantClosedTerm); 
				if (implies == LBool.UNSAT) {
					impliedInterpolants.add(interpolant);
				}
				LBool explies = m_SmtManager.isCovered(interpolantClosedTerm, closedTerm);
				if (explies == LBool.UNSAT) {
					expliedInterpolants.add(interpolant);
				}
				if (implies == LBool.UNSAT && explies == LBool.UNSAT) {
					return interpolant;
				} 
			}
			return null;
		}
		
		private boolean equivalentToFalse(Term term) {
			LBool sat = Util.checkSat(m_SmtManager.getScript(), term);
			switch (sat) {
			case UNSAT:
				return true;
			case SAT:
				return false;
			case UNKNOWN:
				TraceChecker.s_Logger.warn(new DebugMessage(
						"assuming that {0} is not equivalent to false", term));
				return false;
//				throw new UnsupportedOperationException("Unable to decide if " +
//						term + " is equivalent to false");
			default:
				throw new AssertionError();
			}
		}
		
		private boolean equivalentToTrue(Term term) {
			Term negation = m_SmtManager.getScript().term("not", term);
			LBool sat = Util.checkSat(m_SmtManager.getScript(), negation);
			switch (sat) {
			case UNSAT:
				return true;
			case SAT:
				return false;
			case UNKNOWN:
				TraceChecker.s_Logger.warn(new DebugMessage(
						"assuming that {0} is not equivalent to true", term));
				return false;
//				throw new UnsupportedOperationException("Unable to decide if " +
//						term + " is equivalent to true");
			default:
				throw new AssertionError();
			}
		}
		
		
		/**
		 * Given a term "cut up" all its conjuncts. We bring the term in CNF
		 * and return an IPredicate for each conjunct.
		 */
		public Set<IPredicate> cannibalize(Term term) {
			Set<IPredicate> result = new HashSet<IPredicate>();
			Term cnf = (new Cnf(m_SmtManager.getScript())).transform(term);
			Term[] conjuncts = PartialQuantifierElimination.getConjuncts(cnf);
			for (Term conjunct : conjuncts) {
				TermVarsProc tvp = m_SmtManager.computeTermVarsProc(conjunct);
				IPredicate predicate = getOrConstructPredicate(tvp.getFormula(), tvp.getVars(), tvp.getProcedures());
				result.add(predicate);
			}
			return result;
		}
		
		public Set<IPredicate> cannibalizeAll(IPredicate... predicates) {
			final Set<IPredicate> result = new HashSet<IPredicate>();
			for (IPredicate pred : predicates) {
				result.addAll(cannibalize(pred.getFormula()));
			}
			return result;
		}
	}