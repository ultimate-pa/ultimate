package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.automata.tree.PostfixTree;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.TreeEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol.HornClauseFalsePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.script.HornAnnot;

public class TreeAutomizerCEGAR {

	public TreeAutomatonBU<HCTransFormula, HCPredicate> mAbstraction;

	public ITreeRun<HCTransFormula, HCPredicate> mCounterexample;

	private final HCPredicateFactory mPredicateFactory;

	private final Script mBackendSmtSolverScript;

	private int mIteration;

	private ILogger mLogger;

	private final HashMap<Term, Integer> termCounter;
	private final BasePayloadContainer mRootNode;
	private final HCPredicate mInitialPredicate;
	private final HCPredicate mFinalPredicate;

	private HCSsa mSSA;

	/**
	 * IInterpolantGenerator that was used in the current iteration.
	 */
	// protected IInterpolantGenerator mInterpolantGenerator;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected ITreeAutomaton<HCTransFormula, HCPredicate> mInterpolAutomaton;

	public TreeAutomizerCEGAR(IUltimateServiceProvider services, IToolchainStorage storage, String name,
			BasePayloadContainer rootNode, TAPreferences taPrefs, ILogger logger, Script script) {
		mPredicateFactory = new HCPredicateFactory(script);
		mBackendSmtSolverScript = script;
		termCounter = new HashMap<>();
		mLogger = logger;
		mRootNode = rootNode;
		mIteration = 0;

		mInitialPredicate = mPredicateFactory
				.truePredicate(new HornClausePredicateSymbol.HornClauseTruePredicateSymbol());
		mFinalPredicate = mPredicateFactory
				.falsePredicate(new HornClausePredicateSymbol.HornClauseFalsePredicateSymbol());
	}

	protected void getInitialAbstraction() throws AutomataLibraryException {

		final Map<String, IAnnotations> st = mRootNode.getPayload().getAnnotations();
		final HornAnnot annot = (HornAnnot) st.get("HoRNClauses");
		final List<HornClause> hornClauses = (List<HornClause>) annot.getAnnotationsAsMap().get("HoRNClauses");

		mAbstraction = new TreeAutomatonBU<>();
		for (final HornClause clause : hornClauses) {
			final List<HCPredicate> tail = new ArrayList<>();
			for (HornClausePredicateSymbol sym : clause.getTailPredicates()) {
				tail.add(mPredicateFactory.truePredicate(sym));
			}
			if (tail.isEmpty()) {
				tail.add(mInitialPredicate);
			}
			if (clause.getHeadPredicate() instanceof HornClauseFalsePredicateSymbol) {
				mAbstraction.addRule(clause.getTransitionFormula(), tail, mFinalPredicate);
			} else {
				mAbstraction.addRule(clause.getTransitionFormula(), tail,
						mPredicateFactory.truePredicate(clause.getHeadPredicate()));
			}
		}

		mAbstraction.addInitialState(mInitialPredicate);
		mAbstraction.addFinalState(mFinalPredicate);
	}

	// @Override
	protected boolean isAbstractionCorrect() throws AutomataOperationCanceledException {
		final TreeEmptinessCheck<HCTransFormula, HCPredicate> emptiness = new TreeEmptinessCheck<>(mAbstraction);

		mCounterexample = emptiness.getResult();

		if (mCounterexample == null) {
			return true;
		}
		mLogger.info("Found error trace");
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mCounterexample.toString());
		}

		return false;
	}

	protected LBool isCounterexampleFeasible() {
		final TreeChecker checker = new TreeChecker(mCounterexample, mBackendSmtSolverScript, termCounter,
				mInitialPredicate, mFinalPredicate, mLogger);
		mSSA = checker.getSSA();
		return checker.checkTrace();
	}

	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		// Using simple interpolant automaton : the counterexample's automaton.
		// mInterpolAutomaton = mCounterexample.getAutomaton();

		PostfixTree<Term, HCPredicate> postfixT = new PostfixTree<>(mSSA.getFormulasTree());

		Term[] ts = new Term[postfixT.getPostFix().size()];
		for (int i = 0; i < ts.length; ++i) {
			ts[i] = mSSA.getPredicateVariable(postfixT.getPostFix().get(i), mBackendSmtSolverScript);
		}
		int[] idx = new int[postfixT.getStartIdx().size()];
		for (int i = 0; i < idx.length; ++i) {
			idx[i] = postfixT.getStartIdx().get(i);
		}
		Term[] interpolants = mBackendSmtSolverScript.getInterpolants(ts, idx);

		Map<HCPredicate, HCPredicate> predsMap = new HashMap<>();
		for (int i = 0; i < interpolants.length; ++i) {
			HCPredicate p = postfixT.getPostFixStates().get(i);
			predsMap.put(p, new HCPredicate(interpolants[i], p));
		}
		mInterpolAutomaton = ((TreeRun<HCTransFormula, HCPredicate>) mCounterexample).reconstruct(predsMap)
				.getAutomaton();

	}

	private void generalizeCounterExample() {
		// TODO(mostafa): Add more sound edges that can be helpful in reduction.
	}

	protected boolean refineAbstraction() throws AutomataOperationCanceledException, AutomataLibraryException {
		generalizeCounterExample();
		mLogger.debug("Refine begins...");
		mLogger.debug(mAbstraction);
		mLogger.debug(mInterpolAutomaton);
		final ITreeAutomaton<HCTransFormula, HCPredicate> cExample = (new Complement<HCTransFormula, HCPredicate>(
				mInterpolAutomaton, mPredicateFactory)).getResult();
		mLogger.debug(cExample);
		mAbstraction = (TreeAutomatonBU<HCTransFormula, HCPredicate>) (new Intersect<HCTransFormula, HCPredicate>(
				mAbstraction, cExample, mPredicateFactory)).getResult();
		mLogger.debug(mAbstraction);

		mLogger.debug("Refine ends...");

		++mIteration;
		return false;
	}

	public Result iterate() throws AutomataLibraryException {
		getInitialAbstraction();

		mLogger.debug(mAbstraction);
		while (true) {
			mLogger.debug("Iteration #" + (mIteration + 1));
			if (isAbstractionCorrect()) {
				mLogger.debug("The program is safe.");
				return Result.SAFE;
			}
			if (isCounterexampleFeasible() == LBool.SAT) {

				mLogger.debug("The program is unsafe, feasible counterexample.");
				mLogger.debug(mCounterexample.getTree());
				return Result.UNSAFE;

			}
			mLogger.debug("Getting Interpolants...");
			constructInterpolantAutomaton();
			mLogger.debug("Refining abstract model...");
			refineAbstraction();
			mLogger.debug(mAbstraction);
		}
	}

	// @Override
	protected void computeCFGHoareAnnotation() {
		// TODO What is HoareAnnotation?
	}

	// @Override
	public IElement getArtifact() {
		// TODO Auto-generated method stub
		return null;
	}
}
