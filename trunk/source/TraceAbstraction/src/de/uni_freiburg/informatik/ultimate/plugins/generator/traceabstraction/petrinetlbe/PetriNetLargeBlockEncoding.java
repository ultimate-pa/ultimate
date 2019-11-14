/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.CopySubnet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.independencerelation.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.independencerelation.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.independencerelation.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.independencerelation.SyntacticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.independencerelation.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.PetriNetLbe;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * TODO: Documentation
 *
 * @author Elisabeth Schanno
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PetriNetLargeBlockEncoding {

	private final ILogger mLogger;
	private final BoundedPetriNet<IIcfgTransition<?>, IPredicate> mResult;
	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
	private final IcfgEdgeFactory mEdgeFactory;
	private final ManagedScript mManagedScript;
	private final HashRelation<IIcfgTransition<?>, IIcfgTransition<?>> mCoEnabledRelation;

	private final Map<IIcfgTransition<?>, List<IIcfgTransition<?>>> mSequentialCompositions = new HashMap<>();
	private final Map<IIcfgTransition<?>, Triple<TermVariable, IIcfgTransition<?>, IIcfgTransition<?>>> mChoiceCompositions = new HashMap<>();

	private final IIndependenceRelation<?, IIcfgTransition<?>> mMoverCheck;
	private int i = 0;
	private int mMoverChecks = 0;
	private final IUltimateServiceProvider mServices;
	private final PetriNetLargeBlockEncodingStatisticsGenerator mPetriNetLargeBlockEncodingStatistics;

	/**
	 * Performs Large Block Encoding on Petri Nets. Currently, only the Sequence Rule is being used because the backtranslation
	 * of the choice rule does not work.
	 * @param services
	 *            A {@link IUltimateServiceProvider} instance.
	 * @param cfgSmtToolkit
	 *            A {@link CfgSmtToolkit} instance that has to contain all procedures and variables that may occur in
	 *            this {@link IIcfg}.
	 * @param petriNet
	 *            The Petri Net on which the large block encoding should be performed.
	 * @throws AutomataOperationCanceledException
	 *            if operation was canceled.
	 * @throws PetriNetNot1SafeException
	 *            if Petri Net is not 1-safe.
	 */
	public PetriNetLargeBlockEncoding(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet, final PetriNetLbe petriNetLbeSettings)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mServices = services;
		mManagedScript = cfgSmtToolkit.getManagedScript();
		mEdgeFactory = cfgSmtToolkit.getIcfgEdgeFactory();
		mPetriNetLargeBlockEncodingStatistics = new PetriNetLargeBlockEncodingStatisticsGenerator();
		mPetriNetLargeBlockEncodingStatistics.start(PetriNetLargeBlockEncodingStatisticsDefinitions.LbeTime);
		mPetriNetLargeBlockEncodingStatistics.setProgramPointsBefore(petriNet.getPlaces().size());
		mPetriNetLargeBlockEncodingStatistics.setTransitionsBefore(petriNet.getTransitions().size());
		mLogger.info("Starting large block encoding on Petri net that " + petriNet.sizeInformation());
		try {
			final BranchingProcess<IIcfgTransition<?>, IPredicate> bp = new FinitePrefix<>(
					new AutomataLibraryServices(services), petriNet).getResult();
//			mCoEnabledRelation = computeCoEnabledRelation(bp);
			mCoEnabledRelation = computeCoEnabledRelationEfficiently(bp);
			final int coEnabledRelationSize = mCoEnabledRelation.size();
			mLogger.info("Number of co-enabled transitions " + coEnabledRelationSize);
			mPetriNetLargeBlockEncodingStatistics.setCoEnabledTransitionPairs(coEnabledRelationSize);

			final IIndependenceRelation<IPredicate, IIcfgTransition<?>> variableBasedCheckIr = new SyntacticIndependenceRelation<>();
			final CachedIndependenceRelation<IPredicate, IIcfgTransition<?>> cachedVariableBasedIr = new CachedIndependenceRelation<>(variableBasedCheckIr);
			final IIndependenceRelation<IPredicate, IIcfgTransition<?>> semanticBasedCheck;
			switch (petriNetLbeSettings) {
			case OFF:
				throw new IllegalArgumentException("do not call LBE if you don't want to use it");
			case SEMANTIC_BASED_MOVER_CHECK:
				// TODO: Add more detail to log message
				mLogger.info("Semantic Check.");
				semanticBasedCheck = new SemanticIndependenceRelation(mServices, mManagedScript, false, false);
				final CachedIndependenceRelation<IPredicate, IIcfgTransition<?>> cachedSemanticBasedIr = new CachedIndependenceRelation<>(semanticBasedCheck);
				mMoverCheck = new UnionIndependenceRelation<IPredicate, IIcfgTransition<?>>(Arrays.asList(cachedVariableBasedIr, cachedSemanticBasedIr));
				break;
			case VARIABLE_BASED_MOVER_CHECK:
				semanticBasedCheck = null;
				// TODO: Add more detail to log message. Users may wonder:
				// * which variable is checked?
				// * is there also a constant check?
				mLogger.info("Variable Check.");
				mMoverCheck = cachedVariableBasedIr;
				break;
			default:
				throw new AssertionError("unknown value " + petriNetLbeSettings);
			}
			int numberOfFixpointIterations = 1;
			BoundedPetriNet<IIcfgTransition<?>, IPredicate> resultLastIteration =
					CopySubnet.copy(new AutomataLibraryServices(services), petriNet, new HashSet<>(petriNet.getTransitions()), petriNet.getAlphabet());
			BoundedPetriNet<IIcfgTransition<?>, IPredicate> resultCurrentIteration = sequenceRule(services, resultLastIteration);
			while (resultLastIteration.getTransitions().size() != resultCurrentIteration.getTransitions().size()) {
				numberOfFixpointIterations++;
				resultLastIteration = resultCurrentIteration;
				resultCurrentIteration = sequenceRule(services, resultCurrentIteration);
			}
			mPetriNetLargeBlockEncodingStatistics.setNumberOfFixpointIterations(numberOfFixpointIterations);
			mLogger.info("Checked pairs total: " + mMoverChecks);
//			mLogger.info("Positive Checks: " + (mCachedCheck.getPositiveCacheSize() + mCachedCheck2.getPositiveCacheSize()));
//			mLogger.info("Negative Checks: " + (mCachedCheck.getNegativeCacheSize() + mCachedCheck2.getNegativeCacheSize()));
//			mLogger.info("Total Mover Checks: " + (mCachedCheck.getNegativeCacheSize() + mCachedCheck.getPositiveCacheSize() +
//					mCachedCheck2.getNegativeCacheSize() + mCachedCheck2.getPositiveCacheSize()));
			mLogger.info("Total number of compositions: " + i);
			mResult = resultCurrentIteration;
			mPetriNetLargeBlockEncodingStatistics.extractStatistics((SemanticIndependenceRelation) semanticBasedCheck);
			mPetriNetLargeBlockEncodingStatistics.extractStatistics((SyntacticIndependenceRelation) variableBasedCheckIr);
		} catch (final AutomataOperationCanceledException aoce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(petriNet));
			aoce.addRunningTaskInfo(runningTaskInfo);
			throw aoce;
		} catch (final ToolchainCanceledException tce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(petriNet));
			tce.addRunningTaskInfo(runningTaskInfo);
			throw tce;
		} finally {
			mPetriNetLargeBlockEncodingStatistics.stop(PetriNetLargeBlockEncodingStatisticsDefinitions.LbeTime);
		}

//		mPetriNetLargeBlockEncodingStatistics.reportPositiveMoverCheck(mCachedCheck.getPositiveCacheSize() + mCachedCheck2.getPositiveCacheSize());
//		mPetriNetLargeBlockEncodingStatistics.reportNegativeMoverCheck(mCachedCheck.getNegativeCacheSize() + mCachedCheck2.getNegativeCacheSize());
//		mPetriNetLargeBlockEncodingStatistics.reportMoverChecksTotal(mCachedCheck.getNegativeCacheSize() + mCachedCheck.getPositiveCacheSize() +
//				mCachedCheck2.getNegativeCacheSize() + mCachedCheck2.getPositiveCacheSize());
		mPetriNetLargeBlockEncodingStatistics.reportCheckedPairsTotal(mMoverChecks);
		mPetriNetLargeBlockEncodingStatistics.reportTotalNumberOfCompositions(i);
		mPetriNetLargeBlockEncodingStatistics.setProgramPointsAfterwards(mResult.getPlaces().size());
		mPetriNetLargeBlockEncodingStatistics.setTransitionsAfterwards(mResult.getTransitions().size());

	}

	private String generateTimeoutMessage(final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet) {
		return "applying PetriNetLargeBlockEncoding to Petri net that " + petriNet.sizeInformation() + " and "
				+ mCoEnabledRelation.size() + " co-enabled transitions pairs.";
	}

	/**
	 * Performs the choice rule on a Petri Net.
	 * NOTE: This rule is not used yet because the backtranslation does not work.
	 * @param services
	 *            A {@link IUltimateServiceProvider} instance.
	 * @param petriNet
	 *            The Petri Net on which the choice rule should be performed.
	 * @return new Petri Net, where the choice rule had been performed.
	 * @throws AutomataOperationCanceledException
	 *            if operation was canceled.
	 * @throws PetriNetNot1SafeException
	 *            if Petri Net is not 1-safe.
	 */
	private BoundedPetriNet<IIcfgTransition<?>, IPredicate> choiceRule(final IUltimateServiceProvider services,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Collection<ITransition<IIcfgTransition<?>, IPredicate>> transitions = petriNet.getTransitions();
		final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> choiceStack = new ArrayList<>();
		for (final ITransition<IIcfgTransition<?>, IPredicate> t1 : transitions) {
			for (final ITransition<IIcfgTransition<?>, IPredicate> t2 : transitions) {
				if (t1.equals(t2)) {
					continue;
				}
				// Check if Pre- and Postset are identical for t1 and t2.
				if (petriNet.getPredecessors(t1).equals(petriNet.getPredecessors(t2))
						&& petriNet.getSuccessors(t1).equals(petriNet.getSuccessors(t2)) && onlyInternal(t1.getSymbol())
						&& onlyInternal(t2.getSymbol())) {
					final List<IIcfgTransition<?>> cfgTransitionsToRemove = new ArrayList<>();
					cfgTransitionsToRemove.add(t1.getSymbol());
					cfgTransitionsToRemove.add(t2.getSymbol());
					final IcfgEdge choiceIcfgEdge = constructParallelComposition(t1.getSymbol().getSource(),
							t2.getSymbol().getTarget(), cfgTransitionsToRemove);

					// Create new element of choiceStack.
					final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> element = new Triple<>(
							choiceIcfgEdge, t1, t2);
					choiceStack.add(element);
					updateCoEnabledRelation(choiceIcfgEdge, t1.getSymbol(), t2.getSymbol());
					updateChoiceCompositions(choiceIcfgEdge, t1.getSymbol(), t2.getSymbol(), null /* TODO */);
				}
			}
		}
		final BoundedPetriNet<IIcfgTransition<?>, IPredicate> newNet = copyPetriNetWithModification(services, petriNet,
				choiceStack);
		return newNet;
	}

	private void updateChoiceCompositions(final IcfgEdge choiceIcfgEdge, final IIcfgTransition<?> t1, final IIcfgTransition<?> t2,
			final TermVariable indicator) {
		mChoiceCompositions.put(choiceIcfgEdge, new Triple<>(indicator, t1, t2));
	}

	/**
	 * Performs the sequence rule on the Petri Net.
	 * @param services
	 *            A {@link IUltimateServiceProvider} instance.
	 * @param petriNet
	 *            The Petri Net on which the sequence rule should be performed.
	 * @return new Petri Net, where the sequence rule had been performed.
	 * @throws AutomataOperationCanceledException
	 *            if operation was canceled.
	 * @throws PetriNetNot1SafeException
	 *            if Petri Net is not 1-safe.
	 */
	private BoundedPetriNet<IIcfgTransition<?>, IPredicate> sequenceRule(final IUltimateServiceProvider services,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Collection<ITransition<IIcfgTransition<?>, IPredicate>> transitions = petriNet.getTransitions();
		final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> sequentialCompositionStack = new ArrayList<>();
		for (final ITransition<IIcfgTransition<?>, IPredicate> t1 : transitions) {
			final Set<IPredicate> t1PostSet = petriNet.getSuccessors(t1);
			final Set<IPredicate> t1PreSet = petriNet.getPredecessors(t1);
			if (t1PostSet.size() == 1) {
				final IPredicate prePlace = t1PreSet.iterator().next();
				final IPredicate postPlace = t1PostSet.iterator().next();
				// Y to V check.
				if (petriNet.getSuccessors(prePlace).size() == 1 && petriNet.getPredecessors(prePlace).size() > 1) {
					final boolean sequentialCompositionAllowed = petriNet.getPredecessors(prePlace).stream().allMatch(t2 ->
					sequenceRuleCheck(t2, t1, prePlace, sequentialCompositionStack, petriNet));
					if (sequentialCompositionAllowed) {
						for (final ITransition<IIcfgTransition<?>, IPredicate> t2 : petriNet.getPredecessors(prePlace)) {
							// simplify Term resulting TransFormula because various other algorithms
							// in Ultimate have to work with this term
							final boolean simplify = true;
							// try to eliminate auxiliary variables to avoid quantifier alterations
							// subsequent SMT solver calls during verification
							final boolean tryAuxVarElimination = true;
							final IcfgEdge sequentialIcfgEdge = constructSequentialComposition(t2.getSymbol().getSource(),
									t1.getSymbol().getTarget(), t2.getSymbol(), t1.getSymbol(), simplify,
									tryAuxVarElimination);
							// create new element of the sequentialCompositionStack.
							final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> element = new Triple<>(
									sequentialIcfgEdge, t2, t1);
							sequentialCompositionStack.add(element);
							i++;
							//mLogger.info("Element number " + i + " added to the stack. (Y to V)");
							if (mCoEnabledRelation.getImage(t1.getSymbol()).isEmpty()) {
								mPetriNetLargeBlockEncodingStatistics.reportComposition(
										PetriNetLargeBlockEncodingStatisticsDefinitions.TrivialYvCompositions);
							} else {
								mPetriNetLargeBlockEncodingStatistics.reportComposition(
										PetriNetLargeBlockEncodingStatisticsDefinitions.ConcurrentYvCompositions);
							}
							updateCoEnabledRelation(sequentialIcfgEdge, t2.getSymbol(), t1.getSymbol());
							updateSequentialCompositions(sequentialIcfgEdge, t2.getSymbol(), t1.getSymbol());
						}
					}
				}
				else if (petriNet.getPredecessors(postPlace).size() == 1) {
					final boolean sequentialCompositionAllowed = petriNet.getSuccessors(postPlace).stream().allMatch(t2 ->
					sequenceRuleCheck(t1, t2, postPlace, sequentialCompositionStack, petriNet));
					if (sequentialCompositionAllowed) {
						for (final ITransition<IIcfgTransition<?>, IPredicate> t2 : petriNet.getSuccessors(postPlace)) {
							// simplify Term resulting TransFormula because various other algorithms
							// in Ultimate have to work with this term
							final boolean simplify = true;
							// try to eliminate auxiliary variables to avoid quantifier alterations
							// subsequent SMT solver calls during verification
							final boolean tryAuxVarElimination = true;
							final IcfgEdge sequentialIcfgEdge = constructSequentialComposition(t1.getSymbol().getSource(),
									t2.getSymbol().getTarget(), t1.getSymbol(), t2.getSymbol(), simplify,
									tryAuxVarElimination);
							// create new element of the sequentialCompositionStack.
							final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> element = new Triple<>(
									sequentialIcfgEdge, t1, t2);
							sequentialCompositionStack.add(element);
							i++;
							//mLogger.info("Element number " + i + " added to the stack.");
							if (mCoEnabledRelation.getImage(t1.getSymbol()).isEmpty()) {
								mPetriNetLargeBlockEncodingStatistics.reportComposition(
										PetriNetLargeBlockEncodingStatisticsDefinitions.TrivialSequentialCompositions);
							} else {
								mPetriNetLargeBlockEncodingStatistics.reportComposition(
										PetriNetLargeBlockEncodingStatisticsDefinitions.ConcurrentSequentialCompositions);
							}
							updateCoEnabledRelation(sequentialIcfgEdge, t1.getSymbol(), t2.getSymbol());
							updateSequentialCompositions(sequentialIcfgEdge, t1.getSymbol(), t2.getSymbol());
						}
					}
				}
			}
		}
		final BoundedPetriNet<IIcfgTransition<?>, IPredicate> newNet = copyPetriNetWithModification(services, petriNet,
				sequentialCompositionStack);
		return newNet;
	}

	/**
	 * Updates the mSequentialCompositions. This is needed for the backtranslation.
	 * @param sequentialIcfgEdge
	 *            The sequentially composed IcfgEdge.
	 * @param t1
	 *            The first transition that had been sequentially composed.
	 * @param t2
	 *            The second transition that had been sequentially composed.
	 */
	private void updateSequentialCompositions(final IcfgEdge sequentialIcfgEdge, final IIcfgTransition<?> t1, final IIcfgTransition<?> t2) {
		List<IIcfgTransition<?>> left;
		List<IIcfgTransition<?>> right;
		if (mSequentialCompositions.containsKey(t1)) {
			left = mSequentialCompositions.get(t1);
			mSequentialCompositions.remove(t1);
		} else {
			left = new ArrayList<IIcfgTransition<?>>();
			left.add(t1);
		}

		if (mSequentialCompositions.containsKey(t2)) {
			right = mSequentialCompositions.get(t2);
			mSequentialCompositions.remove(t2);
		} else {
			right = new ArrayList<IIcfgTransition<?>>();
			right.add(t2);
		}

		left.addAll(right);
		mSequentialCompositions.put(sequentialIcfgEdge, left);
	}

	/**
	 * Adapted code from BlockEncodingBacktranslator used to translate an execution from the new net to an execution of the old net.
	 * NOTE: Does not handle choice rule yet!
	 * @param execution
	 *            The execution of the new Petri Net.
	 * @return the corresponding execution of the old Petri Net.
	 */
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> translateExecution(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> execution) {
		// TODO: handling of choice rule

		if (execution == null) {
			throw new IllegalArgumentException("execution is null");
		}

		if (!(execution instanceof IcfgProgramExecution)) {
			throw new IllegalArgumentException("argument is not IcfgProgramExecution but " + execution.getClass());

		}
		final IcfgProgramExecution oldIcfgPe = ((IcfgProgramExecution) execution);
		final Map<TermVariable, Boolean>[] oldBranchEncoders = oldIcfgPe.getBranchEncoders();
		assert oldBranchEncoders.length == oldIcfgPe.getLength() : "wrong branchencoders";

		final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> newTrace = new ArrayList<>();
		final List<ProgramState<Term>> newValues = new ArrayList<>();
		final List<Map<TermVariable, Boolean>> newBranchEncoders = new ArrayList<>();

		for (int i = 0; i < oldIcfgPe.getLength(); ++i) {
			final AtomicTraceElement<IIcfgTransition<IcfgLocation>> currentATE = oldIcfgPe.getTraceElement(i);
			final IIcfgTransition<IcfgLocation> transition = currentATE.getTraceElement();

			if (mSequentialCompositions.containsKey(transition)) {
				final List<IIcfgTransition<?>> mappedEdges = mSequentialCompositions.get(transition);
				final Iterator<IIcfgTransition<?>> iter = mappedEdges.iterator();
				while (iter.hasNext()) {
					final IIcfgTransition<?> currentEdge = iter.next();
					// TODO: try to avoid this unchecked cast
					newTrace.add((AtomicTraceElement) AtomicTraceElementBuilder.fromReplaceElementAndStep(currentATE, currentEdge).build());
					if (iter.hasNext()) {
						newValues.add(null);
						newBranchEncoders.add(null);
					}
				}
			} else {
				newTrace.add(currentATE);
			}

			final ProgramState<Term> newProgramState = oldIcfgPe.getProgramState(i);
			newValues.add(newProgramState);
			newBranchEncoders.add(oldBranchEncoders[i]);
		}

		final Map<Integer, ProgramState<Term>> newValuesMap = new HashMap<>();
		newValuesMap.put(-1, oldIcfgPe.getInitialProgramState());
		for (int i = 0; i < newValues.size(); ++i) {
			newValuesMap.put(i, newValues.get(i));
		}

		return new IcfgProgramExecution(newTrace, newValuesMap,
				newBranchEncoders.toArray(new Map[newBranchEncoders.size()]), oldIcfgPe.isConcurrent());
	}

	/**
	 * Checks whether the sequence Rule can be performed.
	 * @param t1
	 *            The first transition that might be sequentially composed.
	 * @param t2
	 *            The second transition that might be sequentially composed.
	 * @param place
	 *            The place connecting t1 and t2.
	 * @param sequentialCompositionStack
	 *            A stack containing Triples (a1, a2, a3), where a1 is the sequential composition of a2 and a3.
	 * @param petriNet
	 *            The Petri Net.
	 * @return true iff the sequence rule can be performed.
	 */
	private boolean sequenceRuleCheck(final ITransition<IIcfgTransition<?>, IPredicate> t1,
			final ITransition<IIcfgTransition<?>, IPredicate> t2, final IPredicate place,
			final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> sequentialCompositionStack,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet) {
		if (petriNet.getPredecessors(t2).size() == 1 && !petriNet.getSuccessors(t2).contains(place)
				&& onlyInternal(t1.getSymbol()) && onlyInternal(t2.getSymbol())) {
			if (isRightMover(t1) || isLeftMover(t2)) {
				for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triple : sequentialCompositionStack) {
					if (triple.getThird() == t1 || triple.getSecond() == t2) {
						return false;
					}
				}
			} else {
				return false;
			}
		} else {
			return false;
		}
		return true;
	}

	/**
	 * Creates a new Petri Net with all the new composed edges and without any of the edges that have been composed.
	 * @param services
	 *            A {@link IUltimateServiceProvider} instance.
	 * @param petriNet
	 *            The original Petri Net.
	 * @param compositionStack
	 *            A Stack that contains Triples (t1, t2, t3), where t1 is the new IcfgEdge consisting of the old ITransitions t2 and t3.
	 * @return a new Petri Net with composed edges and without the edges that are not needed anymore.
	 * @throws AutomataOperationCanceledException
	 *            if operation was canceled.
	 * @throws PetriNetNot1SafeException
	 *            if the Petri Net is not 1-safe.
	 */
	private BoundedPetriNet<IIcfgTransition<?>, IPredicate> copyPetriNetWithModification(
			final IUltimateServiceProvider services, final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet,
			final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> compositionStack)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triplet : compositionStack) {
			petriNet.getAlphabet().add(triplet.getFirst());
			petriNet.addTransition(triplet.getFirst(), petriNet.getPredecessors(triplet.getSecond()),
					petriNet.getSuccessors(triplet.getThird()));
		}

		final Set<ITransition<IIcfgTransition<?>, IPredicate>> transitionsToKeep = new HashSet<>(
				petriNet.getTransitions());

		final Set<IIcfgTransition<?>> newAlphabet = new HashSet<>();
		for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triplet : compositionStack) {
			newAlphabet.add(triplet.getFirst());
			transitionsToKeep.remove(triplet.getSecond());
			transitionsToKeep.remove(triplet.getThird());
		}
		for (final ITransition<IIcfgTransition<?>, IPredicate> transition : transitionsToKeep) {
			newAlphabet.add(transition.getSymbol());
		}
		// Create new net
		final BoundedPetriNet<IIcfgTransition<?>, IPredicate> newNet = CopySubnet
				.copy(new AutomataLibraryServices(services), petriNet, transitionsToKeep, newAlphabet);
		return newNet;
	}

	/**
	 * Updates the mCoEnabledRelation. Since we use the update function, we do not have to compute the branching process multiple times.
	 * @param composedIcfgEdge
	 *            The new IcfgEdge of the Petri Net consisting of t1 and t2.
	 * @param t1
	 *            The first transition that had been composed.
	 * @param t2
	 *            The second transition that had been composed.
	 */
	private void updateCoEnabledRelation(final IcfgEdge composedIcfgEdge, final IIcfgTransition<?> t1, final IIcfgTransition<?> t2) {
		mCoEnabledRelation.replaceDomainElement(t1, composedIcfgEdge);
		mCoEnabledRelation.replaceRangeElement(t1, composedIcfgEdge);
		mCoEnabledRelation.removeDomainElement(t2);
		mCoEnabledRelation.removeRangeElement(t2);
	}

	/**
	 * Computes the mCoEnabledRelation. This relation is needed in order to determine which transitions can be melted.
	 * @param bp
	 *            The branching process of the Petri Net.
	 * @return the co-enabled relation of the Petri Net.
	 */
	private HashRelation<IIcfgTransition<?>, IIcfgTransition<?>> computeCoEnabledRelation(
			final BranchingProcess<IIcfgTransition<?>, IPredicate> bp) {
		final HashRelation<IIcfgTransition<?>, IIcfgTransition<?>> hashRelation = new HashRelation<>();
		final ICoRelation<IIcfgTransition<?>, IPredicate> coRelation = bp.getCoRelation();
		final Collection<Event<IIcfgTransition<?>, IPredicate>> events = bp.getEvents();
		for (final Event<IIcfgTransition<?>, IPredicate> event1 : events) {
			for (final Event<IIcfgTransition<?>, IPredicate> event2 : events) {
				if (event1 == bp.getDummyRoot() || event2 == bp.getDummyRoot()) {
					continue;
				}
				final boolean coEnabled = isInCoRelation(event1, event2, coRelation);
				if (coEnabled) {
					final IIcfgTransition<?> symbol1 = event1.getTransition().getSymbol();
					final IIcfgTransition<?> symbol2 = event2.getTransition().getSymbol();
					hashRelation.addPair(symbol1, symbol2);
				}
			}
		}
		return hashRelation;
	}

	private HashRelation<IIcfgTransition<?>, IIcfgTransition<?>> computeCoEnabledRelationEfficiently(
			final BranchingProcess<IIcfgTransition<?>, IPredicate> bp) {
		final HashRelation<IIcfgTransition<?>, IIcfgTransition<?>> hashRelation = new HashRelation<>();
		final ICoRelation<IIcfgTransition<?>, IPredicate> coRelation = bp.getCoRelation();
		final Collection<Event<IIcfgTransition<?>, IPredicate>> events = bp.getEvents();
		for (final Event<IIcfgTransition<?>, IPredicate> event1 : events) {
			final Set<Event<IIcfgTransition<?>, IPredicate>> coRelatedEvents = coRelation.computeCoRelatatedEvents(event1);
			for (final Event<IIcfgTransition<?>, IPredicate> coRelatedEvent : coRelatedEvents) {
				hashRelation.addPair(event1.getTransition().getSymbol(), coRelatedEvent.getTransition().getSymbol());
			}
		}
		return hashRelation;
	}

	// TODO: use new builtin method? (but correct spelling)
	/**
	 * Checks if two events are in co-relation. (This is needed for the computation of mCoEnabledRelation)
	 * @param e1
	 *            First event.
	 * @param e2
	 *            Second event.
	 * @param coRelation
	 *            The co-relation of the Petri Net unfolding.
	 * @return true iff e1 and e2 are in co-relation.
	 */
	private boolean isInCoRelation(final Event<IIcfgTransition<?>, IPredicate> e1,
			final Event<IIcfgTransition<?>, IPredicate> e2,
			final ICoRelation<IIcfgTransition<?>, IPredicate> coRelation) {
		return e2.getPredecessorConditions().stream().allMatch(condition -> coRelation.isInCoRelation(condition, e1));
	}

	public BoundedPetriNet<IIcfgTransition<?>, IPredicate> getResult() {
		return mResult;
	}
	/**
	 * Checks if a Transition t1 is a left mover with regard to all its co-enabled transitions.
	 * @param t1
	 *            A transition of the Petri Net.
	 * @return true iff t1 is left mover.
	 */
	private boolean isLeftMover(final ITransition<IIcfgTransition<?>, IPredicate> t1) {
		// Filter which elements of coEnabledRelation are relevant.
		final Set<IIcfgTransition<?>> coEnabledTransitions = mCoEnabledRelation.getImage(t1.getSymbol());
		mMoverChecks += coEnabledTransitions.size();
		return coEnabledTransitions.stream().allMatch(t2 -> mMoverCheck.contains(null, t2, t1.getSymbol()));
	}

	/**
	 * Checks if a Transition is a right mover with regard to all its co-enabled transitions.
	 * @params t1
	 *            A transition of the Petri Net.
	 * @return true iff t1 is right mover.
	 */
	private boolean isRightMover(final ITransition<IIcfgTransition<?>, IPredicate> t1) {
		// Filter which elements of coEnabledRelation are relevant.
		final Set<IIcfgTransition<?>> coEnabledTransitions = mCoEnabledRelation.getImage(t1.getSymbol());
		mMoverChecks += coEnabledTransitions.size();
		return coEnabledTransitions.stream().allMatch(t2 -> mMoverCheck.contains(null, t1.getSymbol(), t2));
	}

	// Methods from IcfgEdgeBuilder.
	private static boolean onlyInternal(final IIcfgTransition<?> transition) {
		return transition instanceof IIcfgInternalTransition<?> && !(transition instanceof Summary);
	}

	private static boolean onlyInternal(final List<IIcfgTransition<?>> transitions) {
		return transitions.stream().allMatch(PetriNetLargeBlockEncoding::onlyInternal);
	}

	public IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgTransition<?> first, final IIcfgTransition<?> second, final boolean simplify,
			final boolean tryAuxVarElimination) {
		final List<IIcfgTransition<?>> codeblocks = Arrays.asList(new IIcfgTransition<?>[] { first, second });
		return constructSequentialComposition(source, target, codeblocks, simplify, tryAuxVarElimination);
	}

	private IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final List<IIcfgTransition<?>> transitions, final boolean simplify, final boolean tryAuxVarElimination) {
		assert onlyInternal(transitions) : "You cannot have calls or returns in normal sequential compositions";
		final List<UnmodifiableTransFormula> transFormulas = transitions.stream().map(IcfgUtils::getTransformula)
				.collect(Collectors.toList());
		final UnmodifiableTransFormula tf = TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript,
				simplify, tryAuxVarElimination, false, mXnfConversionTechnique, mSimplificationTechnique,
				transFormulas);
		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, tf);
		ModelUtils.mergeAnnotations(transitions, rtr);
		return rtr;
	}

	public IcfgEdge constructParallelComposition(final IcfgLocation source, final IcfgLocation target,
			final List<IIcfgTransition<?>> transitions) {
		assert onlyInternal(transitions) : "You cannot have calls or returns in normal sequential compositions";
		final List<UnmodifiableTransFormula> transFormulas = transitions.stream().map(IcfgUtils::getTransformula)
				.collect(Collectors.toList());
		final UnmodifiableTransFormula[] tfArray = transFormulas
				.toArray(new UnmodifiableTransFormula[transFormulas.size()]);
		// TODO Matthias 2019-11-13: Serial number should be unique!!!?!
		// Maybe we should move these constructions to the edge factory
		// which can construct unique serial numbers
		final int serialNumber = HashUtils.hashHsieh(293, (Object[]) tfArray);
		final UnmodifiableTransFormula parallelTf = TransFormulaUtils.parallelComposition(mLogger, mServices,
				serialNumber, mManagedScript, null, false, mXnfConversionTechnique, tfArray);
		final LinkedHashMap<TermVariable, IIcfgTransition<?>> branchIndicator2edge = constructBranchIndicatorToEdgeMapping(
				serialNumber, mManagedScript, transitions);
		final TermVariable[] branchIndicatorArray = branchIndicator2edge.keySet()
				.toArray(new TermVariable[branchIndicator2edge.size()]);
		final UnmodifiableTransFormula parallelWithBranchIndicators = TransFormulaUtils.parallelComposition(mLogger,
				mServices, serialNumber, mManagedScript, branchIndicatorArray, false, mXnfConversionTechnique, tfArray);
		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransitionWithBranchEncoders(source, target, null,
				parallelTf, parallelWithBranchIndicators, branchIndicator2edge);
		ModelUtils.mergeAnnotations(transitions, rtr);
		return rtr;
	}

	private static LinkedHashMap<TermVariable, IIcfgTransition<?>> constructBranchIndicatorToEdgeMapping(
			final int serialNumber, final ManagedScript managedScript, final List<IIcfgTransition<?>> transitions) {
		final LinkedHashMap<TermVariable, IIcfgTransition<?>> result = new LinkedHashMap<>();
		managedScript.lock(result);
		for (int i = 0; i < transitions.size(); i++) {
			final String varname = "BraInd" + i + "of" + serialNumber;
			final Sort boolSort = SmtSortUtils.getBoolSort(managedScript.getScript());
			final TermVariable tv = managedScript.constructFreshTermVariable(varname, boolSort);
			result.put(tv, transitions.get(i));
		}
		managedScript.unlock(result);
		return result;
	}

	public PetriNetLargeBlockEncodingBenchmarks getPetriNetLargeBlockEncodingStatistics() {
		return new PetriNetLargeBlockEncodingBenchmarks(mPetriNetLargeBlockEncodingStatistics);
	}



}
