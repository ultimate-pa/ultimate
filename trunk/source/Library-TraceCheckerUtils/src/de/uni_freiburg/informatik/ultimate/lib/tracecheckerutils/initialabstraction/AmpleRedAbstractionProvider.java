/*
 *
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AmpleReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.AmpleReductionConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.RandomDfsOrder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ThreadBasedPersistentSets;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;

/*
 * Analogon to PartialOrderAbstractionProvider
 * no idea what this thing is supposed to do
 * transform an initial abstraction to ?
 * petrinet to nestedwordautomaton?
 *
 * @param <L>: type of transition
 *
 *
 */
// first transform the petrinet using the petrinet2finiteautomaton? then reduce?
public class AmpleRedAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, NestedWordAutomaton<L, IPredicate>> {

	private final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mUnderlying;
	private final IUltimateServiceProvider mServices;
	private final IEmptyStackStateFactory<IPredicate> mStateFactory;
	private final long mDfsOrderSeed;
	private final AutomataLibraryServices mAutomataServices;

	// TODO: Do a check whether the input automaton is deterministic
	public AmpleRedAbstractionProvider(
			final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> underlying,
			final IUltimateServiceProvider services, final IEmptyStackStateFactory<IPredicate> stateFactory,
			final long seed) {
		mUnderlying = underlying;
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(services);
		mStateFactory = stateFactory;
		mDfsOrderSeed = seed;
	}

	@Override
	public NestedWordAutomaton<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {

		final IIndependenceRelation<IPredicate, L> indep =
				IndependenceBuilder.<L> semantic(mServices, icfg.getCfgSmtToolkit().getManagedScript(), false, false)
						.withSyntacticCheck().cached().threadSeparated().build();
		// get persistent sets - should we give the error locs?
		final IPersistentSetChoice<L, IPredicate> persistent =
				new ThreadBasedPersistentSets(mServices, icfg, indep, null, errorLocs, true);
		// get visitor
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> originalAutomaton =
				mUnderlying.getInitialAbstraction(icfg, errorLocs);
		final AmpleReductionConstructingVisitor<L, IPredicate> visitor = new AmpleReductionConstructingVisitor<>(
				originalAutomaton, originalAutomaton::isInitial, originalAutomaton::isFinal,
				originalAutomaton.getVpAlphabet(), mAutomataServices, mStateFactory, persistent);
		// get reduction
		// as we assume a deterministic input automaton, there should only be one initiial state here
		final IPredicate initState = originalAutomaton.getInitialStates().iterator().next();
		// TODO: Do something about the order (order shouldnt matter) // state here
		final AmpleReduction<L, IPredicate> ampleRed = new AmpleReduction<>(mAutomataServices, originalAutomaton,
				new RandomDfsOrder<>(mDfsOrderSeed, false), visitor, initState);
		// get result from visitor.getReductionAutomaton()

		return visitor.getReductionAutomaton();
	}

}
