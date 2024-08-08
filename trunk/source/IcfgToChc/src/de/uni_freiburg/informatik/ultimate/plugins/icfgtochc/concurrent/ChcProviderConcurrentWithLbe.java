package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriLbeInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.IcfgCompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.IcfgToChcObserver.IChcProvider;

/**
 * ChcProvider for concurrent programs based on the petri-net using LBE.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ChcProviderConcurrentWithLbe implements IChcProvider {
	private final ManagedScript mMgdScript;
	private final HcSymbolTable mHcSymbolTable;
	private final IUltimateServiceProvider mServices;

	private static final int MAXIMUM_NUMBER_OF_THREADS = 2;

	public ChcProviderConcurrentWithLbe(final ManagedScript mgdScript, final HcSymbolTable hcSymbolTable,
			final IUltimateServiceProvider services) {
		mMgdScript = mgdScript;
		mHcSymbolTable = hcSymbolTable;
		mServices = services;
	}

	@Override
	public Collection<HornClause> getHornClauses(final IIcfg<IcfgLocation> icfg) {
		final IIcfg<IcfgLocation> petrified = new IcfgPetrifier(mServices, icfg, 2, false).getPetrifiedIcfg();
		final Map<String, Integer> numberOfThreads =
				petrified.getInitialNodes().stream().collect(Collectors.toMap(IcfgLocation::getProcedure, x -> 1));
		final Set<String> unboundedThreads = new HashSet<>();
		final var forksInLoops = IcfgUtils.getForksInLoop(petrified);
		final var instanceMap = petrified.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap();
		for (final var entry : instanceMap.entrySet()) {
			final String instance = entry.getValue().get(0).getThreadInstanceName();
			// TODO: Only add if fork is reachable
			if (forksInLoops.contains(entry.getKey())) {
				numberOfThreads.put(instance, MAXIMUM_NUMBER_OF_THREADS);
				unboundedThreads.add(instance);
			} else {
				numberOfThreads.put(instance, 1);
			}
		}
		final BoundedPetriNet<IcfgEdge, IPredicate> petriNet = getPetriNetWithLbe(petrified, mServices);
		final List<HornClause> result = new ArrayList<>();
		final List<IcfgLocation> errorLocs = getLocations(petriNet.getAcceptingPlaces()).stream()
				.filter(x -> numberOfThreads.containsKey(x.getProcedure())).collect(Collectors.toList());
		final IcfgToChcConcurrent factory = new IcfgToChcConcurrent(numberOfThreads, mMgdScript,
				petrified.getCfgSmtToolkit(), mHcSymbolTable, x -> true);
		result.add(factory.getInitialClause(getLocations(petriNet.getInitialPlaces())));
		result.addAll(factory.getSafetyClauses(errorLocs));
		for (final Transition<IcfgEdge, IPredicate> transition : petriNet.getTransitions()) {
			final IcfgEdge edge = transition.getSymbol();
			final String proc = edge.getPrecedingProcedure();
			if (!numberOfThreads.containsKey(proc) || !numberOfThreads.containsKey(edge.getSucceedingProcedure())) {
				continue;
			}
			final List<IcfgLocation> pre = getLocations(transition.getPredecessors());
			final List<IcfgLocation> post = getLocations(transition.getSuccessors());
			result.addAll(factory.getInductivityClauses(pre, edge, post));
			if (unboundedThreads.contains(proc)) {
				result.add(factory.getNonInterferenceClause(edge));
			}
			// TODO: Special case for a fork to do "nothing"?
			// TODO: What about joins?
		}
		return result;
	}

	private static List<IcfgLocation> getLocations(final Collection<IPredicate> places) {
		final List<IcfgLocation> result = new ArrayList<>();
		for (final IPredicate p : places) {
			if (p instanceof ISLPredicate) {
				result.add(((ISLPredicate) p).getProgramPoint());
			}
		}
		return result;
	}

	private static BoundedPetriNet<IcfgEdge, IPredicate> getPetriNetWithLbe(final IIcfg<IcfgLocation> icfg,
			final IUltimateServiceProvider services) {
		final CfgSmtToolkit csToolkit = icfg.getCfgSmtToolkit();
		final PredicateFactory predicateFactory =
				new PredicateFactory(services, csToolkit.getManagedScript(), csToolkit.getSymbolTable());
		final PetriInitialAbstractionProvider<IcfgEdge> petriNetProvider =
				new PetriInitialAbstractionProvider<>(services, predicateFactory, true);
		final PetriLbeInitialAbstractionProvider<IcfgEdge> lbeProvider =
				new PetriLbeInitialAbstractionProvider<>(services, petriNetProvider, IcfgEdge.class,
						new IndependenceSettings(), new IcfgCompositionFactory(services, csToolkit));
		final Set<IcfgLocation> inUseLocs =
				new HashSet<>(icfg.getCfgSmtToolkit().getConcurrencyInformation().getInUseErrorNodeMap().values());
		final Set<IcfgLocation> errors = icfg.getProcedureErrorNodes().values().stream().flatMap(Collection::stream)
				.filter(x -> !inUseLocs.contains(x)).collect(Collectors.toSet());
		try {
			return lbeProvider.getInitialAbstraction(icfg, errors);
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}
}
