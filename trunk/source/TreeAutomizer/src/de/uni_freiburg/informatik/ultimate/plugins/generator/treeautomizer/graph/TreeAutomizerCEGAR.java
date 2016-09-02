package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.petruchio.EmptinessPetruchio;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.TreeEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil.HCTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil.HornClausePredicateSymbol;

public class TreeAutomizerCEGAR extends AbstractCegarLoop {

	private TreeAutomatonBU<HCTransFormula, IPredicate> mAbstraction;
	
	protected ITreeRun<HCTransFormula, IPredicate> mCounterexample;
	
	private final PredicateFactoryResultChecking predicateFactory;
	
	private final Script mBackendSmtSolverScript;
	
	/**
	 * IInterpolantGenerator that was used in the current iteration.
	 */
	//protected IInterpolantGenerator mInterpolantGenerator;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected ITreeAutomaton<HCTransFormula, IPredicate> mInterpolAutomaton;

	public TreeAutomizerCEGAR(IUltimateServiceProvider services, IToolchainStorage storage, String name,
			RootNode rootNode, SmtManager smtManager, TAPreferences taPrefs, Collection<ProgramPoint> errorLocs,
			ILogger logger, Script script) {
		super(services, storage, name, rootNode, smtManager, taPrefs, errorLocs, logger);
		predicateFactory = new PredicateFactoryResultChecking(smtManager);
		mBackendSmtSolverScript = script;

	}

	@Override
	protected void getInitialAbstraction() throws AutomataOperationCanceledException, AutomataLibraryException {
		// TODO: Compute Abstraction
	}

	@Override
	protected boolean isAbstractionCorrect() throws AutomataOperationCanceledException {
		TreeEmptinessCheck<HCTransFormula, IPredicate> emptiness = new TreeEmptinessCheck<>(mAbstraction);
		
		final TreeAutomatonBU<HCTransFormula, IPredicate> abstraction = mAbstraction;
		mCounterexample = (ITreeRun<HCTransFormula, IPredicate>) emptiness.getResult();
		
		if (mCounterexample == null) {
			return true;
		}
		mLogger.info("Found error trace");
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mCounterexample.getTree().toString());
		}
		
		return false;
		/*
		if (mAbsIntRunner != null)
			mAbsIntRunner.generateFixpoints(mCounterexample, abstraction);
		if (mPref.dumpAutomata())
			dumpNestedRun(mCounterexample, mIterationPW, mLogger);
		final HistogramOfIterable<CodeBlock> traceHistogram = new HistogramOfIterable<CodeBlock>(mCounterexample.getWord());
		mCegarLoopBenchmark.reportTraceHistogramMaximum(traceHistogram.getVisualizationArray()[0]);
		if (mLogger.isInfoEnabled())
			mLogger.info("trace histogram " + traceHistogram.toString());
		*/
	}

	@Override
	protected LBool isCounterexampleFeasible() {
		// TODO Auto-generated method stub
		SSABuilder ssaBuilder = new SSABuilder(mCounterexample, mBackendSmtSolverScript);//preCondition, postCondition)
		HCSsa ssa = ssaBuilder.getSSA();
		
		// TODO(mostafa): Check satsifiability
		return null;
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		// TODO(mostafa): compute Interpolants Automaton properly.
		mInterpolAutomaton = mCounterexample.getAutomaton();
	}
	
	private void generalizeCounterExample() {
		// TODO(mostafa): Add more sound edges that can be helpful in reduction.
	}
	
	@Override
	protected boolean refineAbstraction() throws AutomataOperationCanceledException, AutomataLibraryException {	
		generalizeCounterExample();
		ITreeAutomaton<HCTransFormula, IPredicate> cExample = (new Complement<HCTransFormula, IPredicate>(mCounterexample.getAutomaton(), predicateFactory)).getResult();
		mAbstraction = (TreeAutomatonBU<HCTransFormula, IPredicate>) (new Intersect<HCTransFormula, IPredicate>(mAbstraction, cExample, predicateFactory)).getResult();
		
		++mIteration;
		return false;
	}

	@Override
	protected void computeCFGHoareAnnotation() {
		// TODO What is HoareAnnotation?
	}

	@Override
	public IElement getArtifact() {
		// TODO Auto-generated method stub
		return null;
	}
}
