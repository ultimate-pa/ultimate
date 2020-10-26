/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ICompositionFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.LiptonReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.PetriNetLbe;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SyntacticIndependenceRelation;

/**
 * Performs a Large Block Encoding on Petri nets. This operation performs Lipton reduction ({@link LiptonReduction}) and
 * instantiates the parameters in a way suitable (and sound) for Trace abstraction.
 *
 * Furthermore, it implements backtranslation of {@link IProgramExecution}s containing fused transitions as created by
 * Lipton reductions.
 *
 * @author Elisabeth Schanno
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PetriNetLargeBlockEncoding<L extends IIcfgTransition<?>> {

	private final ILogger mLogger;
	private final BoundedPetriNet<L, IPredicate> mResult;
	private final ManagedScript mManagedScript;

	private final Map<L, List<L>> mSequentialCompositions;
	private final Map<L, Set<L>> mChoiceCompositions;
	private final Map<L, TermVariable> mBranchEncoderMap;

	private final IUltimateServiceProvider mServices;
	private final PetriNetLargeBlockEncodingStatisticsGenerator mStatistics =
			new PetriNetLargeBlockEncodingStatisticsGenerator();

	/**
	 * Performs Large Block Encoding on the given Petri net.
	 *
	 * @param services
	 *            A {@link IUltimateServiceProvider} instance.
	 * @param cfgSmtToolkit
	 *            A {@link CfgSmtToolkit} instance that has to contain all procedures and variables that may occur in
	 *            this {@link IIcfg}.
	 * @param petriNet
	 *            The Petri net on which the large block encoding should be performed.
	 * @param petriNetLbeSettings
	 *            Determines the independence relation to be used.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled.
	 * @throws PetriNetNot1SafeException
	 *             if Petri net is not 1-safe.
	 */
	public PetriNetLargeBlockEncoding(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final BoundedPetriNet<L, IPredicate> petriNet, final PetriNetLbe petriNetLbeSettings,
			final IPLBECompositionFactory<L> compositionFactory)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mServices = services;
		mManagedScript = cfgSmtToolkit.getManagedScript();

		final IIndependenceRelation<IPredicate, L> variableCheck = new SyntacticIndependenceRelation<>();
		final IIndependenceRelation<IPredicate, L> semanticCheck;
		final CachedIndependenceRelation<IPredicate, L> moverCheck;
		switch (petriNetLbeSettings) {
		case OFF:
			throw new IllegalArgumentException("do not call LBE if you don't want to use it");
		case SEMANTIC_BASED_MOVER_CHECK:
			mLogger.info("Petri net LBE is using semantic-based independence relation.");
			semanticCheck = new SemanticIndependenceRelation<>(mServices, mManagedScript, false, false);
			final IIndependenceRelation<IPredicate, L> unionCheck =
					new UnionIndependenceRelation<>(Arrays.asList(variableCheck, semanticCheck));
			moverCheck = new CachedIndependenceRelation<>(unionCheck);
			break;
		case VARIABLE_BASED_MOVER_CHECK:
			semanticCheck = null;
			mLogger.info("Petri net LBE is using variable-based independence relation.");
			moverCheck = new CachedIndependenceRelation<>(variableCheck);
			break;
		default:
			throw new AssertionError("unknown value " + petriNetLbeSettings);
		}

		mLogger.info("Starting large block encoding on Petri net that " + petriNet.sizeInformation());
		try {
			final LiptonReduction<L, IPredicate> lipton = new LiptonReduction<>(new AutomataLibraryServices(services),
					petriNet, compositionFactory, moverCheck);
			mResult = lipton.getResult();
			mSequentialCompositions = lipton.getSequentialCompositions();
			mChoiceCompositions = lipton.getChoiceCompositions();
			mBranchEncoderMap = compositionFactory.getBranchEncoders();

			mStatistics.extractStatistics((SemanticIndependenceRelation<L>) semanticCheck);
			mStatistics.extractStatistics((SyntacticIndependenceRelation<?, L>) variableCheck);
			mStatistics.extractStatistics(moverCheck);
			mStatistics.addLiptonStatistics(lipton.getStatistics());

		} catch (final AutomataOperationCanceledException aoce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(petriNet));
			aoce.addRunningTaskInfo(runningTaskInfo);
			throw aoce;
		} catch (final ToolchainCanceledException tce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(petriNet));
			tce.addRunningTaskInfo(runningTaskInfo);
			throw tce;
		}

	}

	private String generateTimeoutMessage(final BoundedPetriNet<L, IPredicate> petriNet) {
		return "applying " + getClass().getSimpleName() + " to Petri net that " + petriNet.sizeInformation();
	}

	/**
	 * Translates an execution from the new net to an execution of the old net. (Code adapted from
	 * BlockEncodingBacktranslator)
	 *
	 * @param execution
	 *            The execution of the new Petri Net.
	 * @return The corresponding execution of the old Petri Net.
	 */
	// TODO (Dominik 2020-10-26) This duplicates code in BlockEncodingBacktranslator. See if we can use that instead,
	// and get rid of this method.
	public IProgramExecution<L, Term> translateExecution(final IProgramExecution<L, Term> execution) {
		if (execution == null) {
			throw new IllegalArgumentException("execution is null");
		}

		if (!(execution instanceof IcfgProgramExecution)) {
			throw new IllegalArgumentException("argument is not IcfgProgramExecution but " + execution.getClass());

		}
		final IcfgProgramExecution<L> oldIcfgPe = ((IcfgProgramExecution<L>) execution);
		final Map<TermVariable, Boolean>[] oldBranchEncoders = oldIcfgPe.getBranchEncoders();
		assert oldBranchEncoders.length == oldIcfgPe.getLength() : "wrong branchencoders";

		final List<AtomicTraceElement<L>> newTrace = new ArrayList<>();
		final List<ProgramState<Term>> newValues = new ArrayList<>();
		final List<Map<TermVariable, Boolean>> newBranchEncoders = new ArrayList<>();

		for (int i = 0; i < oldIcfgPe.getLength(); ++i) {
			final AtomicTraceElement<L> currentATE = oldIcfgPe.getTraceElement(i);
			final L transition = currentATE.getTraceElement();

			final Collection<L> newTransitions = translateBack(transition, oldBranchEncoders[i]);
			int j = 0;
			for (final L newTransition : newTransitions) {
				newTrace.add(AtomicTraceElementBuilder.fromReplaceElementAndStep(currentATE, newTransition).build());
				j++;

				// If more transitions to come, set the intermediate state to null
				if (j < newTransitions.size()) {
					newValues.add(null);
					newBranchEncoders.add(oldBranchEncoders[i]);
				}
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

		return new IcfgProgramExecution<L>(newTrace, newValuesMap,
				newBranchEncoders.toArray(new Map[newBranchEncoders.size()]), oldIcfgPe.isConcurrent(),
				IcfgProgramExecution.getClassFromAtomicTraceElements(newTrace));
	}

	/**
	 * Translate a transition that is the result of arbitrarily nested sequential and choice compositions back to the
	 * sequence of original transitions.
	 *
	 * @param transition
	 *            The transition to translate back.
	 * @param branchEncoders
	 *            Branch encoders indicating which branch of a choice composition was taken.
	 */
	private Collection<L> translateBack(final L transition, final Map<TermVariable, Boolean> branchEncoders) {
		final ArrayDeque<L> result = new ArrayDeque<>();

		final ArrayDeque<L> stack = new ArrayDeque<>();
		stack.push(transition);

		while (!stack.isEmpty()) {
			final L current = stack.pop();

			if (mSequentialCompositions.containsKey(current)) {
				final List<L> sequence = mSequentialCompositions.get(current);
				assert sequence != null;

				// Put the transitions making up this composition on the stack.
				// Last transition in the sequence is on top.
				for (final L component : sequence) {
					stack.push(component);
				}
			} else if (mChoiceCompositions.containsKey(current)) {
				final Set<L> choices = mChoiceCompositions.get(current);
				assert choices != null;

				if (branchEncoders == null) {
					mLogger.warn("Failed to translate choice composition: Branch encoders not available.");
					result.addFirst(current);
					continue;
				}

				boolean choiceFound = false;
				for (final L choice : choices) {
					assert mBranchEncoderMap.get(choice) != null : "Choice composition is missing branch encoder";
					final TermVariable indicator = mBranchEncoderMap.get(choice);
					assert branchEncoders.get(indicator) != null : "Branch indicator value was unknown";
					if (branchEncoders.get(indicator)) {
						stack.push(choice);
						choiceFound = true;
						break;
					}
				}
				assert choiceFound : "Could not determine correct choice for choice composition";
			} else {
				// Transition is assumed to be original.
				// As the last transition of a sequence is handled first (top of stack, see
				// above), we must prepend this transition to the result (instead of appending).
				result.addFirst(current);
			}
		}
		return result;
	}

	public BoundedPetriNet<L, IPredicate> getResult() {
		return mResult;
	}

	public PetriNetLargeBlockEncodingBenchmarks getPetriNetLargeBlockEncodingStatistics() {
		return new PetriNetLargeBlockEncodingBenchmarks(mStatistics);
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	public interface IPLBECompositionFactory<L> extends ICompositionFactory<L> {

		Map<L, TermVariable> getBranchEncoders();

	}
}
