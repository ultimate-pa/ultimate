package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.InformationStorage;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.IHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantSleepSetOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetDelayReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetNewStateReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetVisitorSearch;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SyntacticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

public class SleepSetCegar<L extends IIcfgTransition<?>> extends BasicCegarLoop<L>{
	
	SleepSetVisitorSearch<L,IPredicate> mVisitor;
	SleepSetMode mSleepSetMode;
	ArrayList<NestedWordAutomaton<L, IPredicate>> mInterpolantAutomataList = new ArrayList<>();

	public SleepSetCegar(DebugIdentifier name, IIcfg rootNode, CfgSmtToolkit csToolkit,
			PredicateFactory predicateFactory, TAPreferences taPrefs, Collection errorLocs,
			InterpolationTechnique interpolation, boolean computeHoareAnnotation, IUltimateServiceProvider services,
			IPLBECompositionFactory compositionFactory, Class transitionClazz) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation, services,
				compositionFactory, transitionClazz);
		mSleepSetMode = mPref.getSleepSetMode();
	}
	
	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		return true;
	}
	
	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;

		final IIndependenceRelation<IPredicate, L> indep = new CachedIndependenceRelation<>(
				new UnionIndependenceRelation<>(Arrays.asList(new SyntacticIndependenceRelation<>(),
						new SemanticIndependenceRelation<>(mServices, mCsToolkit.getManagedScript(), mIteration > 0, true))));
		final ISleepSetOrder<IPredicate, L> order =
				new ConstantSleepSetOrder<>(abstraction.getVpAlphabet().getInternalAlphabet());
		
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> newAbstraction = abstraction;
		for (NestedWordAutomaton<L, IPredicate> interpolantAutomaton : mInterpolantAutomataList) {
			try {
				newAbstraction = new InformationStorage<>(newAbstraction, interpolantAutomaton, mStateFactoryForRefinement, false);
			} catch (AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		mVisitor = new SleepSetVisitorSearch<L, IPredicate>(this::isGoalState);
		if (mSleepSetMode == SleepSetMode.DELAY_SET) {
			new SleepSetDelayReduction(newAbstraction, indep, order, mVisitor);
		} else if (mSleepSetMode == SleepSetMode.NEW_STATES){
			new SleepSetNewStateReduction(newAbstraction, indep, order, mSleepSetStateFactory, mVisitor);
		}
		
		mCounterexample = mVisitor.constructRun();
		

		if (mCounterexample == null) {
			return true;
		}

		return false;
	}
	
	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		super.constructInterpolantAutomaton();
		mInterpolantAutomataList.add(mInterpolAutomaton);
	}
	
	private Boolean isGoalState(IPredicate state) {
		MLPredicate mlstate = (MLPredicate) state;
		boolean isErrorState = Arrays.stream(mlstate.getProgramPoints()).anyMatch(mErrorLocs :: contains);
		return isErrorState && !state.getFormula().toString().equals("false");
	}

}
