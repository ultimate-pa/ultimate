package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;

public class SMTTheoryStateFactoryAndPredicateHelper {

	
	private final BasicPredicateFactory mBasicPredicateFactory;
	private final CfgSmtToolkit mCsToolkit;
	private final ManagedScript mMgdScript;
	
	private final SMTTheoryState mTopState;
	private SMTTheoryState mBottomState;

	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_QUICK;
	private XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private SMTTheoryOperationProvider mArrayTheoryOperationProvider;
	private IUltimateServiceProvider mServices;
	private ILogger mLogger;
	private BasicPredicate mFalsePredicate;
	private Map<Term, IPredicate> mTermToPredicate;
	
	public SMTTheoryStateFactoryAndPredicateHelper(IUltimateServiceProvider services, CfgSmtToolkit csToolkit, 
			SMTTheoryOperationProvider arrayTheoryOperationProvider) {
		mCsToolkit = csToolkit;
		mMgdScript = csToolkit.getManagedScript();
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());

		mArrayTheoryOperationProvider =	arrayTheoryOperationProvider;
		
		mTermToPredicate = new HashMap<>();

		mBasicPredicateFactory = new BasicPredicateFactory(services, csToolkit.getManagedScript(), 
				csToolkit.getSymbolTable(), mSimplificationTechnique, mXnfConversionTechnique);

		csToolkit.getManagedScript().lock(this);
		final Term trueTerm = csToolkit.getManagedScript().term(this, "true");
		final Term falseTerm = csToolkit.getManagedScript().term(this, "false");
		csToolkit.getManagedScript().unlock(this);
		mTopState = getOrConstructState(trueTerm, Collections.emptySet());
		mFalsePredicate = mBasicPredicateFactory.newPredicate(falseTerm);
		mBottomState = new SMTTheoryState(mFalsePredicate, Collections.emptySet(), this);
	}

	/**
	 * @param resTerm
	 * @param variables
	 * @return
	 */
	public SMTTheoryState getOrConstructState(Term resTerm, Set<IProgramVarOrConst> variables) {
		
		final IPredicate pred = getOrConstructPredicate(resTerm, variables);

		return getOrConstructState(pred, variables);
	}

	private IPredicate getOrConstructPredicate(Term resTerm, Set<IProgramVarOrConst> variables) {

		IPredicate pred = mTermToPredicate.get(resTerm);

		if (pred == null) {
			Set<IProgramVar> vars = variables.stream()
					.filter(pvoc -> pvoc instanceof IProgramVar)
					.map(var -> (IProgramVar) var)
					.collect(Collectors.toSet());
			mMgdScript.lock(this);
			mMgdScript.push(this, 1);
			final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(resTerm, mMgdScript.getScript(), 
					mCsToolkit.getSymbolTable());
			mMgdScript.assertTerm(this, tvp.getClosedFormula());
//					PredicateUtils.computeClosedFormula(resTerm, vars, mMgdScript.getScript()));
			final LBool checkSatResult = mMgdScript.checkSat(this);
			mMgdScript.pop(this, 1);
			mMgdScript.unlock(this);

			if (checkSatResult == LBool.UNSAT) {
				pred = mFalsePredicate;
			} else {
				pred = mBasicPredicateFactory.newPredicate(resTerm);
			}
		}
		return pred;
	}

	public SMTTheoryState getOrConstructState(IPredicate predicate, Set<IProgramVarOrConst> newPvocs) {
		if (predicate == mFalsePredicate) {
			return mBottomState;
		}
		return new SMTTheoryState(predicate, newPvocs, this);
	}

	public SMTTheoryState getTopState() {
		return mTopState;
	}

	public SMTTheoryState getBottomState() {
		return mBottomState;
	}

	public SMTTheoryState widen(SMTTheoryState first, SMTTheoryState second) {
		return disjoinFlat(first, second);// TODO does this make sense?
	}

	public SMTTheoryState conjoin(SMTTheoryState first, SMTTheoryState second) {
		if (first.isBottom()) {
			return first;
		}
		if (second.isBottom()) {
			return second;
		}

		final IPredicate conjunction = 
				mBasicPredicateFactory.and(mSimplificationTechnique, first.getPredicate(), second.getPredicate());

		final Set<IProgramVarOrConst> newPvocs = new HashSet<>();
		newPvocs.addAll(first.getVariables());
		newPvocs.addAll(second.getVariables());

		return getOrConstructState(conjunction, newPvocs);

	}

	public SMTTheoryState disjoinFlat(SMTTheoryState first, SMTTheoryState second) {
		if (first.isBottom()) {
			return second;
		}
		if (second.isBottom()) {
			return first;
		}

		/*
		 * for each conjunct in each state: check if it also holds in the other state,
		 * in case keep it.
		 */
		final List<Term> conjunctsThatHoldInBoth = new ArrayList<>();
		final Term[] conjunctsFirst = SmtUtils.getConjuncts(first.getPredicate().getClosedFormula());
		for (Term conjunct : conjunctsFirst) {
			if (second.impliesLiteral(conjunct)) {
				conjunctsThatHoldInBoth.add(conjunct);
			}
		}
		final Term[] conjunctsSecond = SmtUtils.getConjuncts(second.getPredicate().getClosedFormula());
		for (Term conjunct : conjunctsSecond) {
			if (first.impliesLiteral(conjunct)) {
				conjunctsThatHoldInBoth.add(conjunct);
			}
		}

		final Set<IProgramVarOrConst> newPvocs = new HashSet<>();
		newPvocs.addAll(first.getVariables());
		newPvocs.addAll(second.getVariables());
		
		final Term intersectedConjunction = 
				SmtUtils.and(mCsToolkit.getManagedScript().getScript(), conjunctsThatHoldInBoth);

		return getOrConstructState(intersectedConjunction, newPvocs);
	}

	public IPredicate projectExistentially(Set<TermVariable> varsToProject, IPredicate predicate) {
		final Term projected = mArrayTheoryOperationProvider.projectExistentially(varsToProject, 
				predicate.getFormula());
		final Term quantEliminated = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, 
				projected, mSimplificationTechnique, mXnfConversionTechnique);
				
		return mBasicPredicateFactory.newPredicate(quantEliminated);
	}

	public boolean implies(
			SMTTheoryState arrayTheoryState, SMTTheoryState other) {
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		mMgdScript.assertTerm(this, arrayTheoryState.getPredicate().getClosedFormula());
		mMgdScript.assertTerm(this, SmtUtils.not(mMgdScript.getScript(), other.getPredicate().getClosedFormula()));
		final LBool checkSatResult = mMgdScript.checkSat(this);
		mMgdScript.pop(this, 1);
		mMgdScript.unlock(this);
		
		assert checkSatResult != LBool.UNKNOWN;

		return checkSatResult == LBool.UNSAT;
	}

	public boolean impliesLiteral(SMTTheoryState arrayTheoryState, Term literalTerm) {
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		mMgdScript.assertTerm(this, arrayTheoryState.getPredicate().getClosedFormula());
		mMgdScript.assertTerm(this, SmtUtils.not(mMgdScript.getScript(), literalTerm));
		final LBool checkSatResult = mMgdScript.checkSat(this);
		mMgdScript.pop(this, 1);
		mMgdScript.unlock(this);
		
		assert checkSatResult != LBool.UNKNOWN;

		return checkSatResult == LBool.UNSAT;
	}
}
