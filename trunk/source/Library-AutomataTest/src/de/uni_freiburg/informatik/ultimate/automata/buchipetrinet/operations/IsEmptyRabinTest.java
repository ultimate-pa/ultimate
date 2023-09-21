package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import static org.hamcrest.MatcherAssert.assertThat;

import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.RabinIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class IsEmptyRabinTest {

	private AutomataLibraryServices mServices;

	@Before
	public void setUp() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);
	}

	@Test
	public final void testBasic() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, true);
		petriNet.addFinitePlace("p1");
		petriNet.addPlace("p2", false, true);

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p1")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);

		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", notEmpty);
	}

	@Test
	public final void testBasic2() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, true);
		petriNet.addPlace("p2", false, true);
		petriNet.addFinitePlace("p2");

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p1")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);

		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", notEmpty);
	}

	@Test
	public final void testBasic3() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, true);
		petriNet.addFinitePlace("p1");
		petriNet.addPlace("p2", false, true);
		petriNet.addFinitePlace("p2");

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p1")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);

		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", !notEmpty);
	}

	@Test
	public final void test4() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addPlace("p6", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3", "p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2", "p3", "p4")), ImmutableSet.of(Set.of("p5", "p6")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p4")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", notEmpty);

	}

	@Test
	public final void test4f() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addFinitePlace("p5");
		petriNet.addPlace("p6", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3", "p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2", "p3", "p4")), ImmutableSet.of(Set.of("p5", "p6")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p4")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should not be found.", !notEmpty);

	}

	@Test
	public final void test4nf() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addFinitePlace("p1");
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addPlace("p6", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3", "p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2", "p3", "p4")), ImmutableSet.of(Set.of("p5", "p6")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p4")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", notEmpty);

	}

	@Test
	public final void test42() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p4", "p5")), ImmutableSet.of(Set.of("p2", "p3")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", notEmpty);
	}

	@Test
	public final void test422() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addPlace("p6", false, false);
		petriNet.addPlace("p7", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3", "p6")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p4", "p5", "p7")),
				ImmutableSet.of(Set.of("p2", "p3", "p6")));
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p7")));
		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", notEmpty);

	}

	@Test
	public final void testCutoffEvent() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "aa", "b", "c", "d", "u");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("aa", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));

		petriNet.addTransition("u", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p6")));
		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		isempty.checkResult(new StringFactory());
		assertThat("Lasso should be found.", notEmpty);
	}

	@Test
	public final void testCutoffEventF() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "aa", "b", "c", "d", "u");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addFinitePlace("p2");
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("aa", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));

		petriNet.addTransition("u", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p6")));
		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		isempty.checkResult(new StringFactory());
		assertThat("Lasso should be found.", !notEmpty);
	}

	@Test
	public final void testCutoffEventF2() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "aa", "b", "c", "d", "u");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addFinitePlace("p1");
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("aa", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));

		petriNet.addTransition("u", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p6")));
		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		isempty.checkResult(new StringFactory());
		assertThat("Lasso should be found.", notEmpty);
	}

	@Test
	public final void testCutoffEvent3() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "aa", "b", "c", "d");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", true, false);
		petriNet.addPlace("p3", true, false);
		petriNet.addPlace("p4", false, true);

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1", "p2")), ImmutableSet.of(Set.of("p1", "p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p3", "p4")), ImmutableSet.of(Set.of("p3", "p2")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);

		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", notEmpty);
	}

	@Test
	public final void testCutoffEvent3F() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "aa", "b", "c", "d");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", true, false);
		petriNet.addPlace("p3", true, false);
		petriNet.addPlace("p4", false, true);
		petriNet.addFinitePlace("p1");

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1", "p2")), ImmutableSet.of(Set.of("p1", "p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p3", "p4")), ImmutableSet.of(Set.of("p3", "p2")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);

		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", !notEmpty);
	}

	@Test
	public final void testCutoffEvent4() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "aa", "b", "c", "d");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p00", true, false);
		petriNet.addPlace("p0", true, false);
		petriNet.addPlace("p1", false, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, true);

		petriNet.addTransition("c", ImmutableSet.of(Set.of("p0")), ImmutableSet.of(Set.of("p1")));
		petriNet.addTransition("aa", ImmutableSet.of(Set.of("p00")), ImmutableSet.of(Set.of("p2", "p3")));

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1", "p2")), ImmutableSet.of(Set.of("p1", "p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p3", "p4")), ImmutableSet.of(Set.of("p3", "p2")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);

		final boolean notEmpty = !isempty.getResult();
		assertThat("Lasso should be found.", notEmpty);
	}

	@Test
	public final void testPartialConfigurationThesis() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f", "g", "h");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, false);
		petriNet.addPlace("p6", false, false);

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4")));

		petriNet.addTransition("d", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p6")));
		petriNet.addTransition("f", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p3")));

		petriNet.addTransition("g", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("h", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p5")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		isempty.checkResult(new StringFactory());
		assertThat("Lasso should be found.", notEmpty);
	}

	@Test
	public final void testPartialConfigurationThesisF1() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f", "g", "h");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addFinitePlace("p5");

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4")));

		petriNet.addTransition("d", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p6")));
		petriNet.addTransition("f", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p3")));

		petriNet.addTransition("g", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("h", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p5")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		isempty.checkResult(new StringFactory());
		assertThat("Lasso should be found.", !notEmpty);
	}

	@Test
	public final void testPartialConfigurationThesisF2() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f", "g", "h");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addFinitePlace("p1");

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4")));

		petriNet.addTransition("d", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p6")));
		petriNet.addTransition("f", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p3")));

		petriNet.addTransition("g", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("h", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p5")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		isempty.checkResult(new StringFactory());
		assertThat("Lasso should be found.", notEmpty);
	}

	@Test
	public final void testPartialConfigurationThesisF3() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f", "g", "h");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addFinitePlace("p4");

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4")));

		petriNet.addTransition("d", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p6")));
		petriNet.addTransition("f", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p3")));

		petriNet.addTransition("g", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("h", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p5")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		isempty.checkResult(new StringFactory());
		assertThat("Lasso should be found.", !notEmpty);
	}

	@Test
	public final void testPartialConfigurationThesisF4() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f", "g", "h");
		final BoundedRabinPetriNet<String, String> petriNet = new BoundedRabinPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addFinitePlace("p2");

		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4")));

		petriNet.addTransition("d", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p6")));
		petriNet.addTransition("f", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p3")));

		petriNet.addTransition("g", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("h", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p5")));

		final RabinIsEmpty<String, String, StringFactory> isempty = new RabinIsEmpty<>(mServices, petriNet);
		final boolean notEmpty = !isempty.getResult();
		isempty.checkResult(new StringFactory());
		assertThat("Lasso should be found.", notEmpty);
	}
}
