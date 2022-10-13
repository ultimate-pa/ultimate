/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ICompositionFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.LiptonReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SyntacticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

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
 */
public class PetriNetLargeBlockEncoding<L extends IIcfgTransition<?>> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;

	private final BoundedPetriNet<L, IPredicate> mResult;
	private final BlockEncodingBacktranslator mBacktranslator;
	private final PetriNetLargeBlockEncodingStatisticsGenerator mStatistics;

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
			final BoundedPetriNet<L, IPredicate> petriNet, final IndependenceSettings independenceSettings,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> clazz)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		mLogger = services.getLoggingService().getLogger(getClass());
		mServices = services;
		mManagedScript = cfgSmtToolkit.getManagedScript();

		final IIndependenceRelation<IPredicate, L> variableCheck = new SyntacticIndependenceRelation<>();
		final IIndependenceRelation<IPredicate, L> semanticCheck;
		final CachedIndependenceRelation<IPredicate, L> moverCheck;
		switch (independenceSettings.getIndependenceType()) {
		case SEMANTIC:
			mLogger.info("Petri net LBE is using semantic-based independence relation.");
			semanticCheck = new SemanticIndependenceRelation<>(mServices, mManagedScript,
					independenceSettings.useConditional(), !independenceSettings.useSemiCommutativity());
			final IIndependenceRelation<IPredicate, L> unionCheck =
					new UnionIndependenceRelation<>(Arrays.asList(variableCheck, semanticCheck));
			moverCheck = new CachedIndependenceRelation<>(unionCheck);
			break;
		case SYNTACTIC:
			semanticCheck = null;
			mLogger.info("Petri net LBE is using variable-based independence relation.");
			moverCheck = new CachedIndependenceRelation<>(variableCheck);
			break;
		default:
			throw new AssertionError("unknown value " + independenceSettings.getIndependenceType());
		}

		mLogger.info("Starting large block encoding on Petri net that " + petriNet.sizeInformation());
		try {
			final LiptonReduction<L, IPredicate> lipton = new LiptonReduction<>(new AutomataLibraryServices(services),
					petriNet, compositionFactory, moverCheck);
			mResult = lipton.getResult();
			mBacktranslator = createBacktranslator(clazz, lipton, compositionFactory);
			mStatistics = new PetriNetLargeBlockEncodingStatisticsGenerator(lipton.getStatistics(),
					moverCheck.getStatistics());
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

	private BlockEncodingBacktranslator createBacktranslator(final Class<L> clazz,
			final LiptonReduction<L, IPredicate> reduction, final IPLBECompositionFactory<L> compositionFactory) {
		final BlockEncodingBacktranslator translator =
				new BlockEncodingBacktranslator((Class<IIcfgTransition<IcfgLocation>>) clazz, Term.class, mLogger);

		for (final Map.Entry<L, List<L>> seq : reduction.getSequentialCompositions().entrySet()) {
			final L newEdge = seq.getKey();
			for (final L originalEdge : seq.getValue()) {
				translator.mapEdges((IIcfgTransition<IcfgLocation>) newEdge,
						(IIcfgTransition<IcfgLocation>) originalEdge);
			}
		}

		final Map<L, TermVariable> branchEncoders = compositionFactory.getBranchEncoders();
		for (final Map.Entry<L, Set<L>> choice : reduction.getChoiceCompositions().entrySet()) {
			final L newEdge = choice.getKey();
			for (final L originalEdge : choice.getValue()) {
				final TermVariable branchEncoder = branchEncoders.get(originalEdge);
				translator.mapEdges((IIcfgTransition<IcfgLocation>) newEdge,
						(IIcfgTransition<IcfgLocation>) originalEdge, branchEncoder);
			}
		}

		return translator;
	}

	public BoundedPetriNet<L, IPredicate> getResult() {
		return mResult;
	}

	public BlockEncodingBacktranslator getBacktranslator() {
		return mBacktranslator;
	}

	public PetriNetLargeBlockEncodingBenchmarks getStatistics() {
		return new PetriNetLargeBlockEncodingBenchmarks(mStatistics);
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	public interface IPLBECompositionFactory<L> extends ICompositionFactory<L> {
		Map<L, TermVariable> getBranchEncoders();
	}
}
