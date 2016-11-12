package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
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
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class HCPredicateFactory implements IStateFactory<HCPredicate> {

	//final protected boolean mComputeHoareAnnotation;
//	final protected TAPreferences mPref;
	//private final HCPredicate memtpyStack;
	//protected final SmtManager mSmtManager;
	
	private final Script mBackendSmtSolverScript;

	public HCPredicateFactory(final Script backendSmtSolverScript) {
		mBackendSmtSolverScript = backendSmtSolverScript;
	}
	
	public HCPredicate createPredicate(HornClausePredicateSymbol loc) {
		return new HCPredicate(loc, mBackendSmtSolverScript.term(loc.toString()));
	}
	
	public HCPredicate truePredicate(HornClausePredicateSymbol loc) {
		return new HCPredicate(loc, mBackendSmtSolverScript.term("true"));
	}

	public HCPredicate falsePredicate(HornClausePredicateSymbol loc) {
		return new HCPredicate(loc, mBackendSmtSolverScript.term("false"));
	}
	@Override
	public HCPredicate intersection(final HCPredicate p1, final HCPredicate p2) {

		Set<IProgramVar> s = new HashSet<>();
		s.addAll(p1.getVars());
		s.addAll(p2.getVars());
		return new HCPredicate(p1.mProgramPoint, Util.and(mBackendSmtSolverScript, new Term[]{p1.getFormula(), p2.getFormula()}), s);
	}

	@Override
	public HCPredicate minimize(final Collection<HCPredicate> states) {
		final Term[] terms = new Term[states.size()];
		int i = 0;
		Set<IProgramVar> s = new HashSet<>();
		for (final HCPredicate pred : states) {
			terms[i] = pred.getFormula();
			++i;
			s.addAll(pred.getVars());
		}
		
		HornClausePredicateSymbol loc = states.iterator().next().mProgramPoint;
		
		return new HCPredicate(loc, Util.or(mBackendSmtSolverScript, terms), s);
		//final Term disjunction = mSmtManager.getPredicateFactory().or(false, states);
		//final HCPredicate result = mSmtManager.getPredicateFactory().newPredicate(disjunction);
		//return result;
	}

	/*
	@Override
	public HCPredicate determinize(final Map<HCPredicate, Set<HCPredicate>> down2up) {
		if (mComputeHoareAnnotation) {
			final List<HCPredicate> upPredicates = new ArrayList<HCPredicate>();
			for (final HCPredicate caller : down2up.keySet()) {
				for (final HCPredicate current : down2up.get(caller)) {
					if (mSmtManager.getPredicateFactory().isDontCare(current)) {
						return mSmtManager.getPredicateFactory().newDontCarePredicate(null);
					}
					upPredicates.add(current);
				}
			}
			final Term conjunction = mSmtManager.getPredicateFactory().and(upPredicates);
			final HCPredicate result = mSmtManager.getPredicateFactory().newPredicate(conjunction);
			return result;
		} else {
			return mSmtManager.getPredicateFactory().newDontCarePredicate(null);
		}
	}

	@Override
	public HCPredicate createSinkStateContent() {
		return mSmtManager.getPredicateFactory().newPredicate(mSmtManager.getScript().term("true"));
	}

	@Override
	public HCPredicate createEmptyStackState() {
		return memtpyStack;
	}

	@Override
	public HCPredicate createDoubleDeckerContent(final HCPredicate down, final HCPredicate up) {
		throw new UnsupportedOperationException();
	}


	@Override
	public HCPredicate senwa(final HCPredicate entry, final HCPredicate state) {
		assert false : "still used?";
		return mSmtManager.getPredicateFactory().newDontCarePredicate(((SPredicate) state).getProgramPoint());
	}

	@Override
	public HCPredicate buchiComplementFKV(final LevelRankingState<?, HCPredicate> compl) {
		return mSmtManager.getPredicateFactory().newDebugPredicate(compl.toString());
	}

	@Override
	public HCPredicate buchiComplementNCSB(final LevelRankingState<?, HCPredicate> compl) {
		return buchiComplementFKV(compl);
	}

	@Override
	public HCPredicate intersectBuchi(final HCPredicate s1, final HCPredicate s2, final int track) {
		throw new AssertionError(
				"intersect is only required for refinement, not for construction of interpolant automaton");
	}

	@Override
	public HCPredicate getContentOnConcurrentProduct(final HCPredicate c1, final HCPredicate c2) {
		if (!(c2 instanceof ISLPredicate)) {
			throw new IllegalArgumentException("has to be predicate with single location");
		}
		ProgramPoint[] programPoints;
		if (c1 instanceof ISLPredicate) {
			programPoints = new ProgramPoint[2];
			programPoints[0] = ((ISLPredicate) c1).getProgramPoint();
		} else if (c1 instanceof IMLPredicate) {
			final IMLPredicate mlpred = (IMLPredicate) c1;
			final int newLength = mlpred.getProgramPoints().length + 1;
			programPoints = Arrays.copyOf(mlpred.getProgramPoints(), newLength);
		} else {
			throw new UnsupportedOperationException();
		}
		final ProgramPoint c2PP = ((ISLPredicate) c2).getProgramPoint();
		programPoints[programPoints.length - 1] = c2PP;
		final Term conjunction = mSmtManager.getPredicateFactory().and(c1, c2);
		final IMLPredicate result = mSmtManager.getPredicateFactory().newMLPredicate(programPoints, conjunction);
		return result;
	}
	*/
}