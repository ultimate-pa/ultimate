package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import static org.hamcrest.MatcherAssert.assertThat;

import java.util.HashSet;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RabinAccepts;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RabinDeterministicDifference;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class RabinDifferenceTest {

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
	public final void testDiffb() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, true);
		petriNet.addPlace("p2", true, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p1")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, true, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addInternalTransition("q1", "a", "q1");
		buchiAutomata.addInternalTransition("q1", "b", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q2");
		buchiAutomata.addInternalTransition("q2", "a", "q1");

		final RabinDeterministicDifference<String, String> rabinDiff = new RabinDeterministicDifference<>(mServices, petriNet, buchiAutomata);

		final var dif = rabinDiff.getResult();

		final Set<NestedLassoWord<String>> wordsToTestLassoWords = new HashSet<>();
		wordsToTestLassoWords.add(getLassoWord("a", "b"));
		wordsToTestLassoWords.add(getLassoWord("a", "b b"));

		RabinAccepts<String, String> rabinAccepts;
		boolean accepted;

		for (final NestedLassoWord<String> nestedLassoWord : wordsToTestLassoWords) {
			rabinAccepts = new RabinAccepts<>(mServices, dif, nestedLassoWord);
			accepted = rabinAccepts.getResult();
			assertThat(nestedLassoWord.toString() + "is accepted in double Loop Petri net.", accepted);
		}

		final Set<NestedLassoWord<String>> nonAcceptingWords = new HashSet<>();
		nonAcceptingWords.add(getLassoWord("a", "a"));
		nonAcceptingWords.add(getLassoWord("a", "a a"));
		nonAcceptingWords.add(getLassoWord("a", "a b"));
		nonAcceptingWords.add(getLassoWord("a", "b a"));

		for (final NestedLassoWord<String> nestedLassoWord : nonAcceptingWords) {
			rabinAccepts = new RabinAccepts<>(mServices, dif, nestedLassoWord);
			accepted = rabinAccepts.getResult();
			assertThat(nestedLassoWord.toString() + "is not accepted in double Loop Petri net.", !accepted);
		}
	}

	@Test
	public final void testDiff() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, true);
		petriNet.addPlace("p3", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, true, "q2");
		buchiAutomata.addState(false, false, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "c", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "c", "q2");

		final RabinDeterministicDifference<String, String> rabinDiff = new RabinDeterministicDifference<>(mServices, petriNet, buchiAutomata);

		final var dif = rabinDiff.getResult();

		final Set<NestedLassoWord<String>> wordsToTestLassoWords = new HashSet<>();
		wordsToTestLassoWords.add(getLassoWord("a", "b"));
		wordsToTestLassoWords.add(getLassoWord("a", "b b"));

		RabinAccepts<String, String> rabinAccepts;
		boolean accepted;

		for (final NestedLassoWord<String> nestedLassoWord : wordsToTestLassoWords) {
			rabinAccepts = new RabinAccepts<>(mServices, dif, nestedLassoWord);
			accepted = rabinAccepts.getResult();
			assertThat(nestedLassoWord.toString() + "is accepted in double Loop Petri net.", accepted);
		}

		final Set<NestedLassoWord<String>> nonAcceptingWords = new HashSet<>();
		nonAcceptingWords.add(getLassoWord("a", "c"));
		nonAcceptingWords.add(getLassoWord("a", "c c"));
		nonAcceptingWords.add(getLassoWord("a", "b c b"));
		nonAcceptingWords.add(getLassoWord("a", "c c b"));

		for (final NestedLassoWord<String> nestedLassoWord : nonAcceptingWords) {
			rabinAccepts = new RabinAccepts<>(mServices, dif, nestedLassoWord);
			accepted = rabinAccepts.getResult();
			assertThat(nestedLassoWord.toString() + "is not accepted in double Loop Petri net.", !accepted);
		}
	}

	@Test
	public final void testDiff2() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, true);
		petriNet.addPlace("p3", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, true, "q2");
		buchiAutomata.addState(false, false, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "c", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "c", "q3");

		final RabinDeterministicDifference<String, String> rabinDiff = new RabinDeterministicDifference<>(mServices, petriNet, buchiAutomata);

		final var dif = rabinDiff.getResult();

		final Set<NestedLassoWord<String>> wordsToTestLassoWords = new HashSet<>();
		wordsToTestLassoWords.add(getLassoWord("a", "b"));
		wordsToTestLassoWords.add(getLassoWord("a", "b b"));
		wordsToTestLassoWords.add(getLassoWord("a", "b c b"));
		wordsToTestLassoWords.add(getLassoWord("a", "c c b"));

		RabinAccepts<String, String> rabinAccepts;
		boolean accepted;

		for (final NestedLassoWord<String> nestedLassoWord : wordsToTestLassoWords) {
			rabinAccepts = new RabinAccepts<>(mServices, dif, nestedLassoWord);
			accepted = rabinAccepts.getResult();
			assertThat(nestedLassoWord.toString() + "is accepted in double Loop Petri net.", accepted);
		}

		final Set<NestedLassoWord<String>> nonAcceptingWords = new HashSet<>();
		nonAcceptingWords.add(getLassoWord("a", "c"));
		nonAcceptingWords.add(getLassoWord("a", "c c"));

		for (final NestedLassoWord<String> nestedLassoWord : nonAcceptingWords) {
			rabinAccepts = new RabinAccepts<>(mServices, dif, nestedLassoWord);
			accepted = rabinAccepts.getResult();
			assertThat(nestedLassoWord.toString() + "is not accepted in double Loop Petri net.", !accepted);
		}
	}

	@Test
	public final void testDiff3() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, true);
		petriNet.addPlace("p3", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, true, "q1");
		buchiAutomata.addState(false, false, "q2");

		buchiAutomata.addInternalTransition("q1", "c", "q1");
		buchiAutomata.addInternalTransition("q1", "b", "q2");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q2");
		buchiAutomata.addInternalTransition("q2", "c", "q2");

		final RabinDeterministicDifference<String, String> rabinDiff = new RabinDeterministicDifference<>(mServices, petriNet, buchiAutomata);

		final var dif = rabinDiff.getResult();

		final Set<NestedLassoWord<String>> wordsToTestLassoWords = new HashSet<>();
		wordsToTestLassoWords.add(getLassoWord("a", "b"));
		wordsToTestLassoWords.add(getLassoWord("a", "b b"));
		wordsToTestLassoWords.add(getLassoWord("a", "b c b"));
		wordsToTestLassoWords.add(getLassoWord("a", "c c b"));
		wordsToTestLassoWords.add(getLassoWord("a", "c"));
		wordsToTestLassoWords.add(getLassoWord("a", "c c"));

		RabinAccepts<String, String> rabinAccepts;
		boolean accepted;

		for (final NestedLassoWord<String> nestedLassoWord : wordsToTestLassoWords) {
			rabinAccepts = new RabinAccepts<>(mServices, dif, nestedLassoWord);
			accepted = rabinAccepts.getResult();
			assertThat(nestedLassoWord.toString() + "is accepted in double Loop Petri net.", accepted);
		}
	}
}
