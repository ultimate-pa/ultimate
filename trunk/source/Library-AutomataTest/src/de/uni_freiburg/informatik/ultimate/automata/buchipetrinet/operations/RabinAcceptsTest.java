package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import static org.hamcrest.MatcherAssert.assertThat;

import java.util.HashSet;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class RabinAcceptsTest {

	private AutomataLibraryServices mServices;

	// TODO: this might be faulty depending on input.
	private final NestedLassoWord<String> getLassoWord(final String word1, final String word2) {
		return new NestedLassoWord<>(NestedWord.nestedWord(new Word<>(word1.split("\\s"))),
				NestedWord.nestedWord(new Word<>(word2.split("\\s"))));
	}

	@Before
	public void setUp() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);

	}

	@Test
	public void testGetResultWithEmptyStem() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("b", "c");

		final BoundedRabinPetriNet<String, String> net1 = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p2", true, false);
		net1.addPlace("p3", false, true);
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p2")));
		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>());
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b", "c"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);

		RabinAccepts<String, String> buchiPetriAccpts = new RabinAccepts<>(mServices, net1, lassoWord);
		boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Stemless Word is accepted in deterministic Petri net.", accepted);

		net1.addFinitePlace("p3");
		buchiPetriAccpts = new RabinAccepts<>(mServices, net1, lassoWord);
		accepted = buchiPetriAccpts.getResult();
		assertThat("Stemless Word is not accepted in limited deterministic Petri net.", !accepted);
	}

	@Test
	public void testGetResultWithNonTrivialLoopPlaces() throws PetriNetNot1SafeException {

		final Set<String> alphabet = Set.of("a", "b");
		final BoundedRabinPetriNet<String, String> net1 = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, false);
		net1.addPlace("p3", false, false);
		net1.addPlace("p4", false, false);
		net1.addPlace("p5", false, false);
		net1.addPlace("p6", false, true);
		net1.addPlace("p7", false, false);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p4")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p5")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p6")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p7")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p7")), ImmutableSet.of(Set.of("p6")));
		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final RabinAccepts<String, String> buchiPetriAccpts = new RabinAccepts<>(mServices, net1, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Word is accepted in nontrivial Loop Petri net.", accepted);
	}

	@Test
	public void testGetResultWithNonTrivialLoopPlaces2() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b");

		final BoundedRabinPetriNet<String, String> net1 = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, false);
		net1.addPlace("p3", false, false);
		net1.addPlace("p4", false, false);
		net1.addPlace("p5", false, true);
		net1.addPlace("p6", false, false);
		net1.addPlace("p7", false, false);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p4")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p5")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p6")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p7")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p7")), ImmutableSet.of(Set.of("p6")));
		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final RabinAccepts<String, String> buchiPetriAccpts = new RabinAccepts<>(mServices, net1, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Word is accepted in nontrivial Loop Petri net.", !accepted);
	}

	@Test
	public void testGetResultWithNondeterministicTransitions() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c");

		final BoundedRabinPetriNet<String, String> net1 = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, false);
		net1.addPlace("p3", false, true);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p2")));
		final NestedLassoWord<String> lassoWord = getLassoWord("a", "b c");
		// finitePlaceSet.add("p3");
		final RabinAccepts<String, String> buchiPetriAccpts = new RabinAccepts<>(mServices, net1, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Word is accepted in nondeterministic Petri net.", accepted);
	}

	@Test
	public void testGetResultWithNondeterministicTransitionsAndNonAcceptingLoop() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c");

		final BoundedRabinPetriNet<String, String> net1 = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, false);
		net1.addPlace("p3", false, false);
		net1.addPlace("p4", false, false);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p2")));
		final NestedLassoWord<String> lassoWord = getLassoWord("a", "b c");
		final RabinAccepts<String, String> buchiPetriAccpts = new RabinAccepts<>(mServices, net1, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Word is not accepted in nondeterministic Petri net with unaccepting Loop.", !accepted);
	}

	@Test
	public void testGetResultWithAcceptingPlaceInStem() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c");

		final BoundedRabinPetriNet<String, String> net1 = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, true);
		net1.addPlace("p3", false, false);
		net1.addPlace("p4", false, false);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p4")));
		final NestedLassoWord<String> lassoWord = getLassoWord("a", "b c");
		// finitePlaceSet.add("p4");
		final RabinAccepts<String, String> buchiPetriAccpts = new RabinAccepts<>(mServices, net1, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Word is accepted in deterministic Petri net.", !accepted);
	}

	@Test
	public void testGetResultWithDoubleLoop() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c");

		final BoundedRabinPetriNet<String, String> net1 = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		net1.addPlace("p0", true, false);
		net1.addPlace("p1", true, false);
		net1.addPlace("p2", false, true);
		net1.addPlace("p3", false, false);
		net1.addTransition("a", ImmutableSet.of(Set.of("p1", "p0")), ImmutableSet.of(Set.of("p2", "p3")));
		net1.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		net1.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));
		final NestedLassoWord<String> lassoWord = getLassoWord("a", "b c");

		RabinAccepts<String, String> buchiPetriAccpts = new RabinAccepts<>(mServices, net1, lassoWord);

		boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Word is accepted in double Loop Petri net.", accepted);

		final Set<NestedLassoWord<String>> wordsToTestLassoWords = new HashSet<>();
		wordsToTestLassoWords.add(getLassoWord("a", "b"));
		wordsToTestLassoWords.add(getLassoWord("a", "b c b"));
		wordsToTestLassoWords.add(getLassoWord("a", "c c b"));

		for (final NestedLassoWord<String> nestedLassoWord : wordsToTestLassoWords) {
			buchiPetriAccpts = new RabinAccepts<>(mServices, net1, nestedLassoWord);
			accepted = buchiPetriAccpts.getResult();
			assertThat(nestedLassoWord.toString() + "is accepted in double Loop Petri net.", accepted);
		}

		final Set<NestedLassoWord<String>> nonAcceptingWords = new HashSet<>();
		nonAcceptingWords.add(getLassoWord("", "b"));
		nonAcceptingWords.add(getLassoWord("a", "c"));
		nonAcceptingWords.add(getLassoWord("a", "c c"));

		for (final NestedLassoWord<String> nestedLassoWord : nonAcceptingWords) {
			buchiPetriAccpts = new RabinAccepts<>(mServices, net1, nestedLassoWord);
			accepted = buchiPetriAccpts.getResult();
			assertThat(nestedLassoWord.toString() + "is not accepted in double Loop Petri net.", !accepted);
		}
	}
}