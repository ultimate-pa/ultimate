package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SmtUtils;
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
		private final CoverageRelation m_CoverageRelation = new CoverageRelation();
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
		 * Add predicate. Store this predicate without further simplification.
		 * Throw an exception if this PredicateUnifier stores already an
		 * equivalent predicate. 
		 */
		void declarePredicate(IPredicate predicate) {
			HashMap<IPredicate,LBool> impliedPredicates = new HashMap<IPredicate,LBool>();
			HashMap<IPredicate,LBool> expliedPredicates = new HashMap<IPredicate,LBool>();
			IPredicate storedPredicate = compareWithExistingPredicates(predicate.getFormula(), 
					predicate.getVars(), impliedPredicates, expliedPredicates);
			if (storedPredicate == null) {
				addNewPredicate(predicate, impliedPredicates, expliedPredicates);
			} else {
				if (storedPredicate != predicate) {
					throw new AssertionError("There is already an" +
							" equivalent predicate");
				}
			}
		}
		
		public IPredicate getOrConstructPredicate(TermVarsProc tvp) {
			return getOrConstructPredicate(tvp.getFormula(), tvp.getVars(), tvp.getProcedures());
		}
		
		/**
		 * Returns true iff each free variables corresponds to a BoogieVar in
		 * vars. Throws an Exception otherwise.
		 */
		private boolean varsIsSupersetOfFreeTermVariables(Term term, Set<BoogieVar> vars) {
			for (TermVariable tv : term.getFreeVars()) {
				BoogieVar bv = m_SmtManager.getBoogie2Smt().getBoogie2SmtSymbolTable().getBoogieVar(tv);
				if (bv == null) {
					throw new AssertionError("Variable " + tv + 
							" has no corresponding BoogieVar, hence seems " +
							"to be some auxiliary variable and may not " +
							"occur unquantified in the formula of a predicate");
				} else {
					if (!vars.contains(bv)) {
						throw new AssertionError("Variable " + tv + 
								" does not occur in vars");
					}
				}
			}
			return true;
		}
		
		/**
		 * Get the predicate for term. If there is not yet a predicate for term,
		 * construct the predicate using vars.
		 * @param vars The BoogieVars of the TermVariables contained in term.
		 * @param proc All procedures of which vars contains local variables.
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
			HashMap<IPredicate,LBool> impliedPredicates = new HashMap<IPredicate,LBool>();
			HashMap<IPredicate,LBool> expliedPredicates = new HashMap<IPredicate,LBool>();
			p = compareWithExistingPredicates(term, vars, 
									impliedPredicates, expliedPredicates);
			if (p != null) {
				return p;
			}  
			Term simplifiedTerm = m_SmtManager.simplify(term);
			final IPredicate result;
			if (simplifiedTerm == term) {
				//no simplification possible
				result = simplifyPredicate(term, vars, procs);
			} else {
				if (m_Term2Predicates.containsKey(simplifiedTerm)) {
					// this case can occur only if theorem prover says UNKNOWN
					// on equivalence checks
					result = m_Term2Predicates.get(simplifiedTerm);
				} else {
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
					result = simplifyPredicate(simplifiedTerm, newVars, 
							newProcs.toArray(new String[0]));
				}
			}
			addNewPredicate(result, impliedPredicates, expliedPredicates);
			return result;
		}
		
		private IPredicate simplifyPredicate(
				Term term, Set<BoogieVar> vars,	String[] procs) {
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
			assert predicate != null;
			return predicate;
		}
		
		private void addNewPredicate(IPredicate pred, 
				Map<IPredicate, LBool> implied, Map<IPredicate, LBool> explied) {
			m_Term2Predicates.put(pred.getFormula(), pred);
			m_CoverageRelation.addPredicate(pred, implied, explied);
		}
		
		/**
		 * Compare Term term whose free variables represent the BoogieVars vars
		 * with all predicates that this Predicate unifier knows. If there 
		 * exists a predicate for which we can prove that it is equivalent to 
		 * term, this predicate is returned.
		 * Otherwise we return null and HashMaps impliedPredicats and 
		 * expliedPredicates are filled with information about implications 
		 * between term and existing Predicates.
		 * @param term
		 * @param vars
		 * @param impliedPredicats Has to be empty, will be filled with all
		 * IPredicates implied by term.
		 * @param expliedPredicates Has to be empty, will be filled with all
		 * IPredicates that imply term.
		 * @return
		 */
		private IPredicate compareWithExistingPredicates(Term term, Set<BoogieVar> vars,
				HashMap<IPredicate,LBool> impliedPredicats, HashMap<IPredicate,LBool> expliedPredicates) {
			Term closedTerm = SmtManager.computeClosedFormula(term, vars, m_SmtManager.getScript());
			assert impliedPredicats.isEmpty();
			assert expliedPredicates.isEmpty();
			m_SmtManager.getScript().echo(new QuotedObject("begin unification"));
			for (Term interpolantTerm : m_Term2Predicates.keySet()) {
				IPredicate interpolant = m_Term2Predicates.get(interpolantTerm);
				Term interpolantClosedTerm = interpolant.getClosedFormula();
				LBool implies = m_SmtManager.isCovered(closedTerm, interpolantClosedTerm);
				impliedPredicats.put(interpolant, implies);
				LBool explies = m_SmtManager.isCovered(interpolantClosedTerm, closedTerm);
				expliedPredicates.put(interpolant, explies);
				if (implies == LBool.UNSAT && explies == LBool.UNSAT) {
					m_SmtManager.getScript().echo(new QuotedObject("end unification"));
					return interpolant;
				} 
			}
			m_SmtManager.getScript().echo(new QuotedObject("end unification"));
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
			Term[] conjuncts = SmtUtils.getConjuncts(cnf);
			for (Term conjunct : conjuncts) {
				TermVarsProc tvp = m_SmtManager.computeTermVarsProc(conjunct);
				IPredicate predicate = getOrConstructPredicate(tvp);
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
		
		
		public CoverageRelation getCoverageRelation() {
			return m_CoverageRelation;
		}

		public class CoverageRelation implements IPredicateCoverageChecker {
			Map<IPredicate, Map<IPredicate, LBool>> m_Lhs2Rhs2lbool = 
					new HashMap<IPredicate, Map<IPredicate, LBool>>();
			
			void addPredicate(IPredicate pred, Map<IPredicate, LBool> implied, Map<IPredicate, LBool> explied) {
				for (Entry<IPredicate, Map<IPredicate, LBool>> entry  : m_Lhs2Rhs2lbool.entrySet()) {
					LBool lBool = explied.get(entry.getKey());
					assert lBool != null;
					entry.getValue().put(pred, lBool);
				}
				m_Lhs2Rhs2lbool.put(pred, implied);
			}

			@Override
			public LBool isCovered(IPredicate lhs, IPredicate rhs) {
				if (lhs == rhs) {
					return LBool.UNSAT;
				}
				Map<IPredicate, LBool> rhs2LBool = m_Lhs2Rhs2lbool.get(lhs);
				if (rhs2LBool == null) {
					throw new AssertionError("unknown predicate" + lhs);
				} 
				LBool lbool = rhs2LBool.get(rhs);
				if (lbool == null) {
					throw new AssertionError("unknown predicate" + rhs);
				}
				return lbool;
			}
			
		}
	}