package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCVar;
/*
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateWithHistory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
*/
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol.HornClauseDontCareSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class HCPredicateFactory implements IStateFactory<HCPredicate> {

	// final protected boolean mComputeHoareAnnotation;
	// final protected TAPreferences mPref;
	private final HCPredicate memtpyStack;
	// protected final SmtManager mSmtManager;

	private final Script mBackendSmtSolverScript;
	private final SimplifyDDA mSimplifier;

	public HCPredicateFactory(final Script backendSmtSolverScript) {
		mBackendSmtSolverScript = backendSmtSolverScript;
		memtpyStack = createDontCarePredicate(new HornClauseDontCareSymbol());
		mSimplifier = new SimplifyDDA(mBackendSmtSolverScript);
	}

	public HCPredicate createDontCarePredicate(HornClausePredicateSymbol loc) {
		return new HCPredicate(loc, mBackendSmtSolverScript.term("true"), new HashMap<>());
	}

	public HCPredicate createPredicate(HornClausePredicateSymbol loc) {
		return new HCPredicate(loc, mBackendSmtSolverScript.term(loc.toString()), new HashMap<>());
	}

	public HCPredicate truePredicate(HornClausePredicateSymbol loc) {
		return new HCPredicate(loc, mBackendSmtSolverScript.term("true"), new HashMap<>());
	}

	public HCPredicate falsePredicate(HornClausePredicateSymbol loc) {
		return new HCPredicate(loc, mBackendSmtSolverScript.term("false"), new HashMap<>());
	}

	private HCPredicate reduceFormula(final HCPredicate[] preds, boolean andOp) {
		// TODO: Check hashing of TermVariable and HCVar.
		final Set<IProgramVar> progVars = new HashSet<>();
		final Map<Term, HCVar> varsMap = new HashMap<>();

		final Term[] terms = new Term[preds.length];
		final Map<String, Term> invMap = new HashMap<>();
		for (int i = 0; i < preds.length; ++i) {
			final Map<Term, Term> substMap = new HashMap<>();
			for (final Entry<Term, HCVar> v : preds[i].getVarsMap().entrySet()) {
				if (invMap.containsKey(v.getValue().getGloballyUniqueId())) {
					substMap.put(v.getKey(), invMap.get(v.getValue().getGloballyUniqueId()));
				} else {
					invMap.put(v.getValue().getGloballyUniqueId(), v.getKey());
				}
			}
			final Substitution subst = new Substitution(mBackendSmtSolverScript, substMap);
			terms[i] = subst.transform(preds[i].getFormula());
		}

		final HornClausePredicateSymbol loc = preds[0].mProgramPoint;

		int predHash = HashUtils.hashHsieh(mBackendSmtSolverScript.hashCode(), loc, preds);
		for (final HCPredicate p : preds) {
			predHash = HashUtils.hashHsieh(mBackendSmtSolverScript.hashCode(), predHash, p, p.mProgramPoint);
		}
		final Term formula = mSimplifier.getSimplifiedTerm(
				andOp ? Util.and(mBackendSmtSolverScript, terms) : Util.or(mBackendSmtSolverScript, terms));
		
		final Set<String> prodVars = new HashSet<>();
		for (final TermVariable var : formula.getFreeVars()) {
			prodVars.add(var.toString());
		}

		for (int i = 0; i < preds.length; ++i) {
			for (final Entry<Term, HCVar> v : preds[i].getVarsMap().entrySet()) {
				if (prodVars.contains(v.getValue().getTermVariable().toString())) {
					varsMap.put(v.getKey(), v.getValue());
					progVars.add(v.getValue());
				}
			}
		}
		
		return new HCPredicate(loc, predHash, formula, progVars, varsMap);
	}
	
	@Override
	public HCPredicate intersection(final HCPredicate p1, final HCPredicate p2) {
		return reduceFormula(new HCPredicate[]{p1, p2}, true);
		/*
		final Set<IProgramVar> s = new HashSet<>();
		s.addAll(p1.getVars());
		s.addAll(p2.getVars());

		int predHash = HashUtils.hashHsieh(mBackendSmtSolverScript.hashCode(), p1, p1.mProgramPoint, p1.getFormula(),
				p2, p2.mProgramPoint, p2.getFormula());
		final Map<Term, HCVar> mp = new HashMap<>();
		for (final Entry<Term, HCVar> v : p1.getVarsMap().entrySet()) {
			mp.put(v.getKey(), v.getValue());
		}
		for (final Entry<Term, HCVar> v : p2.getVarsMap().entrySet()) {
			mp.put(v.getKey(), v.getValue());
		}
		return new HCPredicate(p1.mProgramPoint, predHash, mSimplifier.getSimplifiedTerm(
				Util.and(mBackendSmtSolverScript, new Term[] { p1.getFormula(), p2.getFormula() })), s, mp);
				*/
	}

	@Override
	public HCPredicate minimize(final Collection<HCPredicate> states) {
		final HCPredicate[] preds = new HCPredicate[states.size()];
		int i = 0;
		for (final HCPredicate pred : states) preds[i++] = pred;
		return reduceFormula(preds, false);
		/*
		final Term[] terms = new Term[states.size()];
		int i = 0;
		final Set<IProgramVar> s = new HashSet<>();
		final Map<Term, HCVar> mp = new HashMap<>();
		for (final HCPredicate pred : states) {
			terms[i] = pred.getFormula();
			++i;
			s.addAll(pred.getVars());

			for (final Entry<Term, HCVar> v : pred.getVarsMap().entrySet()) {
				mp.put(v.getKey(), v.getValue());
			}
		}

		final HornClausePredicateSymbol loc = states.iterator().next().mProgramPoint;

		int predHash = HashUtils.hashHsieh(mBackendSmtSolverScript.hashCode(), loc, states);
		for (final HCPredicate p : states) {
			predHash = HashUtils.hashHsieh(mBackendSmtSolverScript.hashCode(), predHash, p, p.mProgramPoint);
		}

		return new HCPredicate(loc, predHash, mSimplifier.getSimplifiedTerm(Util.or(mBackendSmtSolverScript, terms)), s,
				mp);
				*/
	}

	@Override
	public HCPredicate createEmptyStackState() {
		return memtpyStack;
	}
	/*
	 * @Override public HCPredicate determinize(final Map<HCPredicate,
	 * Set<HCPredicate>> down2up) { if (mComputeHoareAnnotation) { final
	 * List<HCPredicate> upPredicates = new ArrayList<HCPredicate>(); for (final
	 * HCPredicate caller : down2up.keySet()) { for (final HCPredicate current :
	 * down2up.get(caller)) { if
	 * (mSmtManager.getPredicateFactory().isDontCare(current)) { return
	 * mSmtManager.getPredicateFactory().newDontCarePredicate(null); }
	 * upPredicates.add(current); } } final Term conjunction =
	 * mSmtManager.getPredicateFactory().and(upPredicates); final HCPredicate
	 * result = mSmtManager.getPredicateFactory().newPredicate(conjunction);
	 * return result; } else { return
	 * mSmtManager.getPredicateFactory().newDontCarePredicate(null); } }
	 * 
	 * @Override public HCPredicate createSinkStateContent() { return
	 * mSmtManager.getPredicateFactory().newPredicate(mSmtManager.getScript().
	 * term("true")); }
	 * 
	 * 
	 * @Override public HCPredicate createDoubleDeckerContent(final HCPredicate
	 * down, final HCPredicate up) { throw new UnsupportedOperationException();
	 * }
	 * 
	 * 
	 * @Override public HCPredicate senwa(final HCPredicate entry, final
	 * HCPredicate state) { assert false : "still used?"; return
	 * mSmtManager.getPredicateFactory().newDontCarePredicate(((SPredicate)
	 * state).getProgramPoint()); }
	 * 
	 * @Override public HCPredicate buchiComplementFKV(final
	 * LevelRankingState<?, HCPredicate> compl) { return
	 * mSmtManager.getPredicateFactory().newDebugPredicate(compl.toString()); }
	 * 
	 * @Override public HCPredicate buchiComplementNCSB(final
	 * LevelRankingState<?, HCPredicate> compl) { return
	 * buchiComplementFKV(compl); }
	 * 
	 * @Override public HCPredicate intersectBuchi(final HCPredicate s1, final
	 * HCPredicate s2, final int track) { throw new AssertionError(
	 * "intersect is only required for refinement, not for construction of interpolant automaton"
	 * ); }
	 * 
	 * @Override public HCPredicate getContentOnConcurrentProduct(final
	 * HCPredicate c1, final HCPredicate c2) { if (!(c2 instanceof
	 * ISLPredicate)) { throw new IllegalArgumentException(
	 * "has to be predicate with single location"); } ProgramPoint[]
	 * programPoints; if (c1 instanceof ISLPredicate) { programPoints = new
	 * ProgramPoint[2]; programPoints[0] = ((ISLPredicate)
	 * c1).getProgramPoint(); } else if (c1 instanceof IMLPredicate) { final
	 * IMLPredicate mlpred = (IMLPredicate) c1; final int newLength =
	 * mlpred.getProgramPoints().length + 1; programPoints =
	 * Arrays.copyOf(mlpred.getProgramPoints(), newLength); } else { throw new
	 * UnsupportedOperationException(); } final ProgramPoint c2PP =
	 * ((ISLPredicate) c2).getProgramPoint(); programPoints[programPoints.length
	 * - 1] = c2PP; final Term conjunction =
	 * mSmtManager.getPredicateFactory().and(c1, c2); final IMLPredicate result
	 * = mSmtManager.getPredicateFactory().newMLPredicate(programPoints,
	 * conjunction); return result; }
	 */
}