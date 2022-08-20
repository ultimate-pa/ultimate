package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import static org.hamcrest.MatcherAssert.assertThat;

import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class LassoConfigurationCheckerIterativeTest {
	private AutomataLibraryServices mServices;

	@Before
	public void setUp() throws Exception {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);
	}

	@Test
	public final void testLassoConfigurationCheckerIterative()
			throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "bb", "c", "cc", "d", "e", "f");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p22", false, false);
		petriNet.addPlace("p222", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p33", false, false);
		petriNet.addPlace("p333", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p22")));
		petriNet.addTransition("bb", ImmutableSet.of(Set.of("p22")), ImmutableSet.of(Set.of("p222")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p33")));
		petriNet.addTransition("cc", ImmutableSet.of(Set.of("p33")), ImmutableSet.of(Set.of("p333")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p222", "p333")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("f", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p4")));

		final PetriNetUnfolder<String, String> unfolder =
				new PetriNetUnfolder<>(mServices, petriNet, PetriNetUnfolder.EventOrderEnum.ERV, false, false);

		final BranchingProcess<String, String> mUnfolding = unfolder.getFinitePrefix();

		final LassoConfigurationCheckerIterative<String, String> configurationChecker =
				new LassoConfigurationCheckerIterative<>(mUnfolding);
		for (final Event<String, String> event : mUnfolding.getEvents()) {
			configurationChecker.update(event);
		}

		final boolean test = !configurationChecker.getLassoConfigurations().isEmpty();
		assertThat("Lasso should be found.", test);
	}

	@Test
	public final void testLassoConfigurationChecker2()
			throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "bb", "c", "cc", "d", "e", "f");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addPlace("p4", false, true);
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p2")));

		final PetriNetUnfolder<String, String> unfolder =
				new PetriNetUnfolder<>(mServices, petriNet, PetriNetUnfolder.EventOrderEnum.ERV, false, false);

		final BranchingProcess<String, String> mUnfolding = unfolder.getFinitePrefix();

		final LassoConfigurationCheckerIterative<String, String> configurationChecker =
				new LassoConfigurationCheckerIterative<>(mUnfolding);
		for (final Event<String, String> event : mUnfolding.getEvents()) {
			configurationChecker.update(event);
		}

		final boolean test = !configurationChecker.getLassoConfigurations().isEmpty();
		assertThat("Lasso should be found.", test);
	}

}
