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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class BuchiPetrinetBuchiIntersectionTest {

	private AutomataLibraryServices mServices;

	@Before
	public void setUp() throws Exception {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);
	}

	@Test
	public final void testBuchiPetrinetBuchiIntersection() throws PetriNetNot1SafeException {
		Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, true);
		petriNet.addPlace("p3", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));

		StringFactory factory = new StringFactory();

		VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addState(false, true, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q2");

		StringFactory factory2 = new StringFactory();

		BuchiPetrinetBuchiIntersection<String, String> intersection =
				new BuchiPetrinetBuchiIntersection<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b", "b"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiPetrinetAccepts<String, String> buchiPetriAccpts =
				new BuchiPetrinetAccepts<>(mServices, intersection, lassoWord);

		boolean accepted = (boolean) buchiPetriAccpts.getResult();

		assertThat("Intersection accepts word in intersection.", accepted);
	}

	@Test
	public final void testBuchiPetrinetBuchiIntersection2() throws PetriNetNot1SafeException {
		Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, true);
		petriNet.addPlace("p3", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));

		StringFactory factory = new StringFactory();

		VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addState(false, true, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q2");

		StringFactory factory2 = new StringFactory();

		BuchiPetrinetBuchiIntersection<String, String> intersection =
				new BuchiPetrinetBuchiIntersection<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b", "c"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiPetrinetAccepts<String, String> buchiPetriAccpts =
				new BuchiPetrinetAccepts<>(mServices, intersection, lassoWord);

		boolean accepted = (boolean) buchiPetriAccpts.getResult();

		assertThat("Intersection accepts word in intersection.", !accepted);
	}

	@Test
	public final void testBuchiPetrinetBuchiIntersection3() throws PetriNetNot1SafeException {
		Set<String> alphabet = Set.of("a", "b", "c");
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

		StringFactory factory = new StringFactory();

		VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addState(false, true, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q2");

		StringFactory factory2 = new StringFactory();

		BuchiPetrinetBuchiIntersection<String, String> intersection =
				new BuchiPetrinetBuchiIntersection<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b", "b"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiPetrinetAccepts<String, String> buchiPetriAccpts =
				new BuchiPetrinetAccepts<>(mServices, intersection, lassoWord);

		boolean accepted = (boolean) buchiPetriAccpts.getResult();

		assertThat("Intersection accepts word in intersection.", accepted);
	}

	@Test
	public final void testBuchiPetrinetBuchiIntersection4() throws PetriNetNot1SafeException {
		Set<String> alphabet = Set.of("a", "b", "c");
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

		StringFactory factory = new StringFactory();

		VpAlphabet<String> buchiAlphabet = new VpAlphabet<>(alphabet);

		final NestedWordAutomaton<String, String> buchiAutomata =
				new NestedWordAutomaton<>(mServices, buchiAlphabet, factory);

		buchiAutomata.addState(true, false, "q1");
		buchiAutomata.addState(false, false, "q2");
		buchiAutomata.addState(false, true, "q3");
		buchiAutomata.addInternalTransition("q1", "a", "q2");
		buchiAutomata.addInternalTransition("q2", "b", "q3");
		buchiAutomata.addInternalTransition("q3", "b", "q2");

		StringFactory factory2 = new StringFactory();

		BuchiPetrinetBuchiIntersection<String, String> intersection =
				new BuchiPetrinetBuchiIntersection<>(petriNet, buchiAutomata, factory2);

		final NestedWord<String> nestedword1 = NestedWord.nestedWord(new Word<>("a"));
		final NestedWord<String> nestedword2 = NestedWord.nestedWord(new Word<>("b", "c"));
		final NestedLassoWord<String> lassoWord = new NestedLassoWord<>(nestedword1, nestedword2);
		final BuchiPetrinetAccepts<String, String> buchiPetriAccpts =
				new BuchiPetrinetAccepts<>(mServices, intersection, lassoWord);

		boolean accepted = (boolean) buchiPetriAccpts.getResult();

		assertThat("Intersection accepts word in intersection.", !accepted);
	}

	/*
	 * @Test public final void testGetAlphabet() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testSize() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testSizeInformation() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testTransformToUltimateModel() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testGetInitialPlaces() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testGetSuccessorsITransitionOfLETTERPLACE() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testGetPredecessorsITransitionOfLETTERPLACE() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testGetSuccessorsPLACE() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testGetPredecessorsPLACE() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testGetSuccessorTransitionProvidersHashRelationOfPLACEPLACE() {
	 * fail("Not yet implemented"); }
	 * 
	 * @Test public final void testGetSuccessorTransitionProvidersSetOfPLACESetOfPLACE() { fail("Not yet implemented");
	 * }
	 * 
	 * @Test public final void testIsAcceptingMarkingOfLETTERPLACE() { fail("Not yet implemented"); }
	 * 
	 * @Test public final void testIsAcceptingPLACE() { fail("Not yet implemented"); }
	 */

}
