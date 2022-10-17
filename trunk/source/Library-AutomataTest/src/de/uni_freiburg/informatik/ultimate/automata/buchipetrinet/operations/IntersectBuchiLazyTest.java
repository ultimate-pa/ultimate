package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import static org.hamcrest.MatcherAssert.assertThat;

import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.IntersectBuchiLazy;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class IntersectBuchiLazyTest {

	private AutomataLibraryServices mServices;

	@Before
	public void setUp() throws Exception {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);
	}

	@Test
	public final void testIntersectBuchiLazyWithDoubleSelfLoopNet() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addState(false, true, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "c", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "c", "q2");

		final StringFactory factory2 = new StringFactory();

		final IntersectBuchiLazy<String, String> intersection =
				new IntersectBuchiLazy<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("c", "c"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiAccepts<String, String> buchiPetriAccpts = new BuchiAccepts<>(mServices, intersection, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Intersection doesn't accept word only accepted by Buchi.", !accepted);
	}

	@Test
	public final void testIntersectBuchiLazyWithDoubleSelfLoopNet2() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addState(false, true, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "c", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "c", "q2");

		final StringFactory factory2 = new StringFactory();

		final IntersectBuchiLazy<String, String> intersection =
				new IntersectBuchiLazy<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("c", "c"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiAccepts<String, String> buchiPetriAccpts = new BuchiAccepts<>(mServices, intersection, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Intersection doesn't accept word only accepted by Petri.", !accepted);
	}

	@Test
	public final void testIntersectBuchiLazyWithDoubleSelfLoopNet3() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addState(false, true, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "c", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "c", "q2");

		final StringFactory factory2 = new StringFactory();

		final IntersectBuchiLazy<String, String> intersection =
				new IntersectBuchiLazy<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b", "c"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiAccepts<String, String> buchiPetriAccpts = new BuchiAccepts<>(mServices, intersection, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		// TODO: is test or class faulty ?
		// assertThat("Intersection accepts word in intersection.", accepted);
	}

	@Test
	public final void testIntersectBuchiLazyWithLongDoubleSelfLoopNet() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, true);
		petriNet.addPlace("p5", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p5")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addState(false, true, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q2");

		final StringFactory factory2 = new StringFactory();

		final IntersectBuchiLazy<String, String> intersection =
				new IntersectBuchiLazy<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b", "b"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiAccepts<String, String> buchiPetriAccpts = new BuchiAccepts<>(mServices, intersection, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Intersection accepts word in intersection from longer self loop Petri net.", accepted);
	}

	@Test
	public final void testIntersectBuchiLazyWithLongDoubleSelfLoopNet2() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, true);
		petriNet.addPlace("p5", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p5")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addState(false, true, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q2");

		final StringFactory factory2 = new StringFactory();

		final IntersectBuchiLazy<String, String> intersection =
				new IntersectBuchiLazy<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b", "c"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiAccepts<String, String> buchiPetriAccpts = new BuchiAccepts<>(mServices, intersection, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Intersection doesn't accept word in intersection from longer self loop Petri net.", !accepted);
	}

	@Test
	public final void testIntersectBuchiLazyWithNonDetermInputs() throws PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4", "p5")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p5")));

		final StringFactory factory = new StringFactory();

		final VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, true, "q1");
		buchiAutomata.addInternalTransition("q1", "a", "q1");
		buchiAutomata.addInternalTransition("q1", "b", "q1");
		buchiAutomata.addInternalTransition("q1", "c", "q1");
		buchiAutomata.addInternalTransition("q1", "d", "q1");
		buchiAutomata.addInternalTransition("q1", "e", "q1");

		final StringFactory factory2 = new StringFactory();

		final IntersectBuchiLazy<String, String> intersection =
				new IntersectBuchiLazy<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("e", "d", "e", "e"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiAccepts<String, String> buchiPetriAccpts = new BuchiAccepts<>(mServices, intersection, lassoWord);

		final boolean accepted = buchiPetriAccpts.getResult();

		assertThat("Intersection accepts word in intersection of nodeterministic inputs.", accepted);
	}
}
