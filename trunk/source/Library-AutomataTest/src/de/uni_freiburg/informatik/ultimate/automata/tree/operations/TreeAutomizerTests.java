/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import org.junit.Before;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Operation of a treeAutomaton accepts a given Run.
 *
 * @author mostafa (mostafa.amin93@gmail.com)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class TreeAutomizerTests {

	private static final String SYM_Q3 = "Q3";
	private static final String SYM_Q2 = "Q2";
	private static final String SYM_Q1 = "Q1";
	private static final String SYM_Q0 = "Q0";
	private static final String SYM_E = "E";
	private static final String SYM_F = "F";
	private static final String SYM_T = "T";
	private static final String SYM_I = "I";
	private static final String SYM_Y = "Y";
	private static final String SYM_X = "X";
	private static final String SYM_BOOL_LIST = "BoolList";
	private static final String SYM_BOOL = "Bool";
	private static final String SYM_NAT_LIST = "NatList";
	private static final String SYM_NAT = "NAT";
	private static final String SYM_INIT_A = "_";

	private AutomataLibraryServices mServices;
	private ILogger mLogger;

	@Before
	public void setUp() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);
		mLogger = services.getLoggingService().getLogger(getClass());
	}

//	@Test
//	public void testAccepts() {
//		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
//
//		treeA.addInitialState(SYM_INIT_A);
//		treeA.addFinalState(SYM_NAT_LIST);
//		treeA.addRule(
//				new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_NAT));
//		treeA.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[] { SYM_NAT })), SYM_NAT));
//		treeA.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })),
//				SYM_NAT_LIST));
//		treeA.addRule(new TreeAutomatonRule<>("cons",
//				new ArrayList<>(Arrays.asList(new String[] { SYM_NAT, SYM_NAT_LIST })), SYM_NAT_LIST));
//
//		// cons(0, cons(s(0), nil))
//		final Tree<String> nil = new Tree<>("nil");
//		final Tree<String> zero1 = new Tree<>("0");
//		final Tree<String> zero2 = new Tree<>("0");
//		final ArrayList<Tree<String>> z1 = new ArrayList<>();
//		z1.add(zero2);
//		final Tree<String> one = new Tree<>("s", z1);
//
//		final ArrayList<Tree<String>> e2 = new ArrayList<>();
//		e2.add(one);
//		e2.add(nil);
//		final Tree<String> elm2 = new Tree<>("cons", e2);
//
//		final ArrayList<Tree<String>> e1 = new ArrayList<>();
//		e1.add(zero1);
//		e1.add(elm2);
//		final Tree<String> run = new Tree<>("f", e1);
//
//		final IUltimateServiceProvider usp = UltimateMocks.createUltimateServiceProviderMock();
//		final AutomataLibraryServices services = new AutomataLibraryServices(usp);
//
//		final Accepts<String, String> op = new Accepts<>(services, treeA, run);
//
//		mLogger.info(run);
//		mLogger.info(op.getResult());
//	}
//
//	@Test
//	public void testComplement() {
//		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
//		final TreeAutomatonBU<String, String> treeB = new TreeAutomatonBU<>();
//
//		treeA.addInitialState(SYM_INIT_A);
//		treeA.addFinalState(SYM_NAT_LIST);
//		treeA.addRule(
//				new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_NAT));
//		treeA.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[] { SYM_NAT })), SYM_NAT));
//		treeA.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })),
//				SYM_NAT_LIST));
//		treeA.addRule(new TreeAutomatonRule<>("cons",
//				new ArrayList<>(Arrays.asList(new String[] { SYM_NAT, SYM_NAT_LIST })), SYM_NAT_LIST));
//
//		treeB.addInitialState(SYM_INIT_A);
//		treeB.addFinalState(SYM_BOOL_LIST);
//		treeB.addRule(
//				new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_BOOL));
//		treeB.addRule(
//				new TreeAutomatonRule<>("1", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_BOOL));
//		treeB.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })),
//				SYM_BOOL_LIST));
//		treeB.addRule(new TreeAutomatonRule<>("cons",
//				new ArrayList<>(Arrays.asList(new String[] { SYM_BOOL, SYM_BOOL_LIST })), SYM_BOOL_LIST));
//
//		final IUltimateServiceProvider usp = UltimateMocks.createUltimateServiceProviderMock();
//		final AutomataLibraryServices services = new AutomataLibraryServices(usp);
//
//		final StringFactory fac = new StringFactory();
//		final Complement<String, String> com = new Complement<>(services, fac, treeB);
//
//		final Intersect<String, String> op = new Intersect<>(services, fac, treeA, com.getResult());
//		final ITreeAutomatonBU<String, String> res = op.getResult();
//
//		mLogger.info(treeA.toString() + "\n");
//		mLogger.info(treeB.toString() + "\n");
//		mLogger.info(com.getResult() + "\n");
//		mLogger.info(res + "\n");
//		mLogger.info(((TreeAutomatonBU<String, String>) res).DebugString() + "\n");
//	}
//
//	@Test
//	public void testDeterminize() {
//		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
//
//		treeA.addInitialState(SYM_Q0);
//		treeA.addFinalState(SYM_Q3);
//		treeA.addRule(new TreeAutomatonRule<>(SYM_F, new ArrayList<>(Arrays.asList(new String[] { SYM_Q0, SYM_Q1 })),
//				SYM_Q2));
//		treeA.addRule(new TreeAutomatonRule<>(SYM_F, new ArrayList<>(Arrays.asList(new String[] { SYM_Q0, SYM_Q1 })),
//				SYM_Q3));
//		treeA.addRule(new TreeAutomatonRule<>("G", new ArrayList<>(Arrays.asList(new String[] { SYM_Q2 })), SYM_Q3));
//		treeA.addRule(new TreeAutomatonRule<>("G", new ArrayList<>(Arrays.asList(new String[] { SYM_Q3 })), SYM_Q3));
//		treeA.addRule(
//				new TreeAutomatonRule<>("H", new ArrayList<>(Arrays.asList(new String[] { SYM_Q0, SYM_Q2 })), SYM_Q1));
//		treeA.addRule(
//				new TreeAutomatonRule<>("H", new ArrayList<>(Arrays.asList(new String[] { SYM_Q0, SYM_Q3 })), SYM_Q1));
//
//		final IUltimateServiceProvider usp = UltimateMocks.createUltimateServiceProviderMock();
//		final AutomataLibraryServices services = new AutomataLibraryServices(usp);
//
//		final StringFactory fac = new StringFactory();
//		final Determinize<String, String> op = new Determinize<>(services, fac, treeA);
//		final ITreeAutomatonBU<String, String> res = op.getResult();
//
//		mLogger.info(treeA.toString() + "\n");
//		mLogger.info(res.toString() + "\n");
//
//		final TreeAutomatonBU<String, String> treeB = new TreeAutomatonBU<>();
//
//		treeB.addInitialState(SYM_INIT_A);
//		treeB.addFinalState(SYM_NAT_LIST);
//		treeB.addRule(
//				new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_NAT));
//		treeB.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[] { SYM_NAT })), SYM_NAT));
//		treeB.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })),
//				SYM_NAT_LIST));
//		treeB.addRule(new TreeAutomatonRule<>("cons",
//				new ArrayList<>(Arrays.asList(new String[] { SYM_NAT, SYM_NAT_LIST })), SYM_NAT_LIST));
//
//		final Determinize<String, String> opB = new Determinize<>(services, fac, treeB);
//		final ITreeAutomatonBU<String, String> resB = opB.getResult();
//
//		mLogger.info(treeB.toString() + "\n");
//		mLogger.info(resB.toString() + "\n");
//
//	}
//
//	@Test
//	public void testIntersect() {
//		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
//		final TreeAutomatonBU<String, String> treeB = new TreeAutomatonBU<>();
//
//		treeA.addInitialState(SYM_INIT_A);
//		treeA.addFinalState(SYM_NAT_LIST);
//		treeA.addRule(
//				new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_NAT));
//		treeA.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[] { SYM_NAT })), SYM_NAT));
//		treeA.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })),
//				SYM_NAT_LIST));
//		treeA.addRule(new TreeAutomatonRule<>("cons",
//				new ArrayList<>(Arrays.asList(new String[] { SYM_NAT, SYM_NAT_LIST })), SYM_NAT_LIST));
//
//		treeB.addInitialState(SYM_INIT_A);
//		treeB.addFinalState(SYM_BOOL_LIST);
//		treeB.addRule(
//				new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_BOOL));
//		treeB.addRule(
//				new TreeAutomatonRule<>("1", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_BOOL));
//		treeB.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })),
//				SYM_BOOL_LIST));
//		treeB.addRule(new TreeAutomatonRule<>("cons",
//				new ArrayList<>(Arrays.asList(new String[] { SYM_BOOL, SYM_BOOL_LIST })), SYM_BOOL_LIST));
//
//		final IUltimateServiceProvider usp = UltimateMocks.createUltimateServiceProviderMock();
//		final AutomataLibraryServices services = new AutomataLibraryServices(usp);
//
//		final StringFactory fac = new StringFactory();
//		final Intersect<String, String> op = new Intersect<>(services, fac, treeA, treeB);
//		final ITreeAutomatonBU<String, String> res = op.getResult();
//
//		mLogger.info(treeA.toString() + "\n");
//		mLogger.info(treeB.toString() + "\n");
//		mLogger.info(res + "\n");
//		mLogger.info(((TreeAutomatonBU<String, String>) res).DebugString() + "\n");
//
//		final TreeAutomatonBU<Character, String> tree1 = new TreeAutomatonBU<>();
//		tree1.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[] { SYM_T })), SYM_I));
//		tree1.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[] { SYM_I })), SYM_I));
//		tree1.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[] { SYM_I })), SYM_F));
//		tree1.addFinalState(SYM_F);
//		tree1.addInitialState(SYM_T);
//
//		final TreeAutomatonBU<Character, String> tree2 = new TreeAutomatonBU<>();
//		tree2.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[] { SYM_T })), SYM_I));
//		tree2.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[] { SYM_T })), SYM_E));
//		tree2.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[] { SYM_T })), SYM_E));
//
//		tree2.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[] { SYM_I })), SYM_E));
//		tree2.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[] { SYM_I })), SYM_E));
//		tree2.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[] { SYM_I })), SYM_F));
//
//		tree2.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[] { SYM_F })), SYM_E));
//		tree2.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[] { SYM_F })), SYM_E));
//		tree2.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[] { SYM_F })), SYM_E));
//
//		tree2.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[] { SYM_E })), SYM_E));
//		tree2.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[] { SYM_E })), SYM_E));
//		tree2.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[] { SYM_E })), SYM_E));
//		tree2.addInitialState(SYM_T);
//		tree2.addFinalState(SYM_I);
//		tree2.addFinalState(SYM_T);
//		tree2.addFinalState(SYM_E);
//
//		mLogger.info(tree1);
//		mLogger.info(tree2);
//		final Intersect<Character, String> oo = new Intersect<>(services, fac, tree1, tree2);
//		final Minimize<Character, String> oo2 = new Minimize<>(services, fac, oo.getResult());
//		mLogger.info(oo2.getResult());
//	}

//	@Test
//	public void testMinimize() {
//
//		final HashSet<Integer> x = new HashSet<>();
//		for (int i = 0; i < 15; ++i) {
//			x.add(i + 1);
//		}
//		final DisjointSet<Integer> st = new DisjointSet<>(x);
//
//		for (int i = 1; i < 15; i += 2) {
//			st.union(i, i + 2);
//		}
//		st.union(3, 1);
//		for (final Iterator<Set<Integer>> it = st.getParitionsIterator(); it.hasNext();) {
//			mLogger.info(it.next());
//		}
//		for (int i = 1; i <= 15; ++i) {
//			mLogger.info(i + " " + st.find(i));
//		}
//		for (int i = 1; i <= 15; ++i) {
//			mLogger.info(i + " " + st.getPartition(i));
//		}
//
//		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
//		treeA.addInitialState(SYM_INIT_A);
//		treeA.addFinalState(SYM_Y);
//		treeA.addRule(
//				new TreeAutomatonRule<>(SYM_I, new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_X));
//		treeA.addRule(
//				new TreeAutomatonRule<>(SYM_I, new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_Y));
//		treeA.addRule(new TreeAutomatonRule<>(SYM_F, new ArrayList<>(Arrays.asList(new String[] { SYM_X })), SYM_X));
//		treeA.addRule(new TreeAutomatonRule<>(SYM_F, new ArrayList<>(Arrays.asList(new String[] { SYM_X })), SYM_Y));
//		treeA.addRule(new TreeAutomatonRule<>(SYM_F, new ArrayList<>(Arrays.asList(new String[] { SYM_Y })), SYM_Y));
//
//		final IUltimateServiceProvider usp = UltimateMocks.createUltimateServiceProviderMock();
//		final AutomataLibraryServices services = new AutomataLibraryServices(usp);
//
//		mLogger.info(treeA.toString() + "\n");
//		final Determinize<String, String> det = new Determinize<>(services, new StringFactory(), treeA);
//		mLogger.info(det.getResult());
//		final Minimize<String, String> op = new Minimize<>(services, new StringFactory(), det.getResult());
//		mLogger.info(op.getResult());
//
//	}
//
//	@Test
//	public void testTotalize() {
//		/*
//		 * TreeAutomatonBU<Character, String> tree = new TreeAutomatonBU<>(); tree.addFinalState("F");
//		 * tree.addInitialState("T");
//		 *
//		 * ArrayList<String> src1 = new ArrayList<>();
//		 *
//		 * src1.add("T"); tree.addRule(new TreeAutomatonRule<Character, String>('a', src1, "I"));
//		 *
//		 * ArrayList<String> src2 = new ArrayList<>(); src2.add("I"); tree.addRule(new TreeAutomatonRule<Character,
//		 * String>('x', src2, "F"));
//		 *
//		 * Totalize<Character, String> op = new Totalize<>(tree, new StringFactory()); mLogger.info(tree);
//		 * mLogger.info(op.getResult());
//		 *
//		 */
//		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
//
//		treeA.addInitialState(SYM_INIT_A);
//		treeA.addFinalState(SYM_NAT_LIST);
//		treeA.addRule(
//				new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), SYM_NAT));
//		treeA.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[] { SYM_NAT })), SYM_NAT));
//		treeA.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })),
//				SYM_NAT_LIST));
//		treeA.addRule(new TreeAutomatonRule<>("cons",
//				new ArrayList<>(Arrays.asList(new String[] { SYM_NAT, SYM_NAT_LIST })), SYM_NAT_LIST));
//
//		final IUltimateServiceProvider usp = UltimateMocks.createUltimateServiceProviderMock();
//		final AutomataLibraryServices services = new AutomataLibraryServices(usp);
//
//		final Totalize<String, String> op2 = new Totalize<>(services, new StringFactory(), treeA);
//		mLogger.info(treeA);
//		mLogger.info(op2.getResult());
//
//	}
//
//	@Test
//	public void testEmptinessCheck() {
//		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
//
//		final String NAT = "N", NatList = "L", EmptyList = "EL";
//
//		treeA.addInitialState(SYM_INIT_A);
//		treeA.addFinalState(NatList);
//		treeA.addRule(new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), NAT));
//		treeA.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[] { NAT })), NAT));
//		treeA.addRule(
//				new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[] { SYM_INIT_A })), EmptyList));
//		treeA.addRule(new TreeAutomatonRule<>("cons", new ArrayList<>(Arrays.asList(new String[] { NAT, EmptyList })),
//				NatList));
//		treeA.addRule(new TreeAutomatonRule<>("cons", new ArrayList<>(Arrays.asList(new String[] { NAT, NatList })),
//				NatList));
//
//		final IUltimateServiceProvider usp = UltimateMocks.createUltimateServiceProviderMock();
//		final AutomataLibraryServices services = new AutomataLibraryServices(usp);
//
//		final TreeEmptinessCheck<String, String> op = new TreeEmptinessCheck<>(services, treeA);
//		final TreeRun<String, String> res = op.getTreeRun();
//
//		mLogger.info(treeA.toString());
//		mLogger.info("");
//		mLogger.info(res.toString());
//		mLogger.info("");
//		mLogger.info(res.getTree().toString());
//		mLogger.info("");
//		mLogger.info(res.getAutomaton().toString());
//	}
}
