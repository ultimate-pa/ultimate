package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import static org.hamcrest.MatcherAssert.assertThat;

import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class LazyBuchiPetriNet2FiniteAutomatonTest {
	private AutomataLibraryServices mServices;

	@Before
	public void setUp() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);
	}

	@Test
	public final void test1() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4", "p5")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p5")));

		NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("c"));
		NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);

		final StringFactory factory = new StringFactory();
		final LazyBuchiPetriNet2FiniteAutomaton<String, String> petri2Buchi =
				new LazyBuchiPetriNet2FiniteAutomaton<>(mServices, factory, factory, petriNet, null);
		final BuchiAccepts<String, String> buchiAccepts = new BuchiAccepts<>(mServices, petri2Buchi, lassoWord);
		assertThat("should be same language", buchiAccepts.getResult());

		nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		nestedword2 = NestedWord.nestedWord(new Word<>("b"));
		lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);

		final BuchiAccepts<String, String> buchiAccepts2 = new BuchiAccepts<>(mServices, petri2Buchi, lassoWord);
		assertThat("should be same language", !buchiAccepts2.getResult());

		nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		nestedword2 = NestedWord.nestedWord(new Word<>("b", "c"));
		lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);

		final BuchiAccepts<String, String> buchiAccepts3 = new BuchiAccepts<>(mServices, petri2Buchi, lassoWord);
		assertThat("should be same language", buchiAccepts3.getResult());
	}

}
