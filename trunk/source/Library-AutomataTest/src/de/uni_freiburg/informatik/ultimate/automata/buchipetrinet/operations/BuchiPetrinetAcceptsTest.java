package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import static org.hamcrest.MatcherAssert.assertThat;

import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class BuchiPetrinetAcceptsTest {

	private AutomataLibraryServices mServices;
	private ILogger mLogger;

	@Before
	public void setUp() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);
		mLogger = services.getLoggingService().getLogger(getClass());
	}

	@Test
	public void testGetResult() throws PetriNetNot1SafeException {
		Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> net1 = new BoundedPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, false);
		net1.addPlace("p3", false, true);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p2")));
		final String[] word1 = { "a" };
		final String[] word2 = { "b", "c" };
		final int[] nesting1 = { -2 };
		final int[] nesting2 = { -2, -2 };
		final NestedWord<String> nestedword1 = new NestedWord<>(word1, nesting1);
		final NestedWord<String> nestedword2 = new NestedWord<>(word2, nesting2);
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiPetrinetAccepts<String, String> buchiPetriAccpts =
				new BuchiPetrinetAccepts<>(mServices, net1, lassoWord);

		boolean accepted = (boolean) buchiPetriAccpts.getResult();

		assertThat("Word is accepted in deterministic Petri net.", accepted);
	}

	@Test
	public void testGetResultWithEmptyStem() throws PetriNetNot1SafeException {
		Set<String> alphabet = Set.of("b", "c");
		final BoundedPetriNet<String, String> net1 = new BoundedPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p2", true, false);
		net1.addPlace("p3", false, true);
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p2")));
		final String[] word1 = {};
		final String[] word2 = { "b", "c" };
		final int[] nesting1 = {};
		final int[] nesting2 = { -2, -2 };
		final NestedWord<String> nestedword1 = new NestedWord<>(word1, nesting1);
		final NestedWord<String> nestedword2 = new NestedWord<>(word2, nesting2);
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiPetrinetAccepts<String, String> buchiPetriAccpts =
				new BuchiPetrinetAccepts<>(mServices, net1, lassoWord);

		boolean accepted = (boolean) buchiPetriAccpts.getResult();

		assertThat("Word is accepted in deterministic Petri net.", accepted);
	}

	@Test
	public void testGetResultWithLongerStemAndLasso() throws PetriNetNot1SafeException {
		Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f");
		final BoundedPetriNet<String, String> net1 = new BoundedPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, false);
		net1.addPlace("p3", false, false);
		net1.addPlace("p4", false, false);
		net1.addPlace("p5", false, true);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p4")));
		net1.addTransition("d", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p5")));
		net1.addTransition("e", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p3")));

		net1.addTransition("f", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p4")));
		final String[] word1 = { "a", "b" };
		final String[] word2 = { "c", "d", "e" };
		final int[] nesting1 = { -2, -2 };
		final int[] nesting2 = { -2, -2, -2 };
		final NestedWord<String> nestedword1 = new NestedWord<>(word1, nesting1);
		final NestedWord<String> nestedword2 = new NestedWord<>(word2, nesting2);
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiPetrinetAccepts<String, String> buchiPetriAccpts =
				new BuchiPetrinetAccepts<>(mServices, net1, lassoWord);

		boolean accepted = (boolean) buchiPetriAccpts.getResult();

		assertThat("Long Word is accepted in deterministic Petri net.", accepted);
	}

	@Test
	public void testGetResultWithNondeterministicTransitions() throws PetriNetNot1SafeException {
		Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> net1 = new BoundedPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, false);
		net1.addPlace("p3", false, true);
		net1.addPlace("p4", false, false);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p2")));
		final String[] word1 = { "a" };
		final String[] word2 = { "b", "c" };
		final int[] nesting1 = { -2 };
		final int[] nesting2 = { -2, -2 };
		final NestedWord<String> nestedword1 = new NestedWord<>(word1, nesting1);
		final NestedWord<String> nestedword2 = new NestedWord<>(word2, nesting2);
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiPetrinetAccepts<String, String> buchiPetriAccpts =
				new BuchiPetrinetAccepts<>(mServices, net1, lassoWord);

		boolean accepted = (boolean) buchiPetriAccpts.getResult();

		assertThat("Word is accepted in nondeterministic Petri net.", accepted);
	}

	@Test
	public void testGetResultWithNondeterministicTransitionsAndNonAcceptingLoop() throws PetriNetNot1SafeException {
		Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> net1 = new BoundedPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, false);
		net1.addPlace("p3", false, false);
		net1.addPlace("p4", false, false);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p2")));
		final String[] word1 = { "a" };
		final String[] word2 = { "b", "c" };
		final int[] nesting1 = { -2 };
		final int[] nesting2 = { -2, -2 };
		final NestedWord<String> nestedword1 = new NestedWord<>(word1, nesting1);
		final NestedWord<String> nestedword2 = new NestedWord<>(word2, nesting2);
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiPetrinetAccepts<String, String> buchiPetriAccpts =
				new BuchiPetrinetAccepts<>(mServices, net1, lassoWord);

		boolean accepted = (boolean) buchiPetriAccpts.getResult();

		assertThat("Word is not accepted in nondeterministic Petri net with unaccepting Loop.", !accepted);
	}

}