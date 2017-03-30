/**
 *
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem;

import static org.junit.Assert.assertEquals;

import java.io.FileInputStream;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.Unmarshaller;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ObjectFactory;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;
import de.uni_freiburg.informatik.ultimate.test.ConsoleLogger;

/**
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class ParallelCompositionGeneratorTest {
	
	/**
	 * Test method for
	 * {@link de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.ParallelCompositionGenerator#computeParallelComposition(de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton, de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton)}
	 * .
	 */
	@Test
	public void testComputeParallelComposition() throws Exception {
		final ILogger logger = new ConsoleLogger();
		// TEST1: aut1: 1 location, 0 transitions, aut2: 1 location, 0 transitions
		System.out.println("Starting Test 1..");
		long startTime = System.nanoTime();
		String file =
				"../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test1.xml";
		FileInputStream fis = new FileInputStream(file);
		final JAXBContext jaxContext = JAXBContext.newInstance(ObjectFactory.class);
		final Unmarshaller unmarshaller = jaxContext.createUnmarshaller();
		Sspaceex spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		HybridModel system = new HybridModel(spaceEx, logger);
		HybridAutomaton merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y]", merge.getLocalParameters().toString());
		assertEquals(
				"{1=loc_loc1_loc1_(1), Invariant: x <= 10 & y <= 10, Flow: x == 10 & y == 10, IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals("[]", merge.getTransitions().toString());
		long estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
		// TEST2: aut1: 1 location, 0 transitions, aut2: 2 locations, 1 transition
		System.out.println("Starting Test 2..");
		startTime = System.nanoTime();
		file = "../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test2.xml";
		fis = new FileInputStream(file);
		spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		system = new HybridModel(spaceEx, logger);
		merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y]", merge.getLocalParameters().toString());
		assertEquals(
				"{1=loc_loc1_loc1_(1), Invariant: x <= 10 & y <= 10, Flow: x == 10 & y == 10, IsForbidden?: false, "
						+ "2=loc_loc2_loc1_(2), Invariant: x <= 10, Flow: x == 10, IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals("[(1) === (); {} ===> (2)]", merge.getTransitions().toString());
		estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
		// TEST3: aut1: 3 locations, 1 sync transition, 1 discrete transition , aut2: 3 locations, 1 sync transition, 1
		// discrete transition
		System.out.println("Starting Test 3..");
		startTime = System.nanoTime();
		file = "../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test3.xml";
		fis = new FileInputStream(file);
		spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		system = new HybridModel(spaceEx, logger);
		merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y]", merge.getLocalParameters().toString());
		assertEquals("[jump1]", merge.getLabels().toString());
		// @formatter:off
		assertEquals(
				"{1=loc_loc1_loc1_(1), Invariant: x <= 4 & y <= 4, Flow: x==1 & y==1, IsForbidden?: false, "
						+ "2=loc_loc2_loc2_(2), Invariant: x <= 5 & y <= 5, Flow: x==1 & y==1, IsForbidden?: false, "
						+ "3=loc_loc3_loc2_(3), Invariant: x <= 6 & y <= 5, Flow: x==1 & y==1, IsForbidden?: false, "
						+ "4=loc_loc2_loc3_(4), Invariant: x <= 5 & y <= 6, Flow: x==1 & y==1, IsForbidden?: false, "
						+ "5=loc_loc3_loc3_(5), Invariant: x <= 6 & y <= 6, Flow: x==1 & y==1, IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals(
				"[(1) === (); {x==0 & y==0}; Label: jump1 ===> (2), "
				+ "(2) === (); {} ===> (4), "
				+ "(2) === (); {} ===> (3), "
				+ "(4) === (); {} ===> (5), "
				+ "(3) === (); {} ===> (5)]",
				merge.getTransitions().toString());
		// @formatter:on
		estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
		// TEST4: aut1: 3 locations, 1 sync transition, 1 discrete transition , aut2: 3 locations, 1 sync transition, 1
		// discrete transition
		System.out.println("Starting Test 4..");
		startTime = System.nanoTime();
		file = "../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test4.xml";
		fis = new FileInputStream(file);
		spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		system = new HybridModel(spaceEx, logger);
		merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y]", merge.getLocalParameters().toString());
		assertEquals("[jump1]", merge.getLabels().toString());
		//@formatter:off
		assertEquals(
				"{1=loc_loc1_loc1_(1), Invariant: x <= 4 & y <= 4, Flow: x==1 & y==1, IsForbidden?: false, "
						+ "2=loc_loc2_loc1_(2), Invariant: x <= 5 & y <= 4, Flow: x==1 & y==1, IsForbidden?: false, "
						+ "3=loc_loc3_loc2_(3), Invariant: x <= 6 & y <= 5, Flow: x==1 & y==1, IsForbidden?: false, "
						+ "4=loc_loc3_loc3_(4), Invariant: x <= 6 & y <= 6, Flow: x==1 & y==1, IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals(
				"[(1) === (); {} ===> (2), "
				+ "(2) === (); {x==0 & y==0}; Label: jump1 ===> (3), "
				+ "(3) === (); {} ===> (4)]",
				merge.getTransitions().toString());
		//@formatter:on
		estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
		/*
		 * Test 5, 3 automata with single locations, no transitions
		 */
		System.out.println("Starting Test 5..");
		startTime = System.nanoTime();
		file = "../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test5.xml";
		fis = new FileInputStream(file);
		spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		system = new HybridModel(spaceEx, logger);
		merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y, z]", merge.getLocalParameters().toString());
		assertEquals("[]", merge.getLabels().toString());
		assertEquals(
				"{1=loc_loc1_loc1_loc1_(1), Invariant: x <= 5 & y <= 5 & z <= 5, Flow: x==4 & y==4 & z==4, IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals("[]", merge.getTransitions().toString());
		estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
		/*
		 * Test 6, 3 automata with two locations, 1 sync transition in each
		 */
		System.out.println("Starting Test 6..");
		startTime = System.nanoTime();
		file = "../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test6.xml";
		fis = new FileInputStream(file);
		spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		system = new HybridModel(spaceEx, logger);
		merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y, z]", merge.getLocalParameters().toString());
		assertEquals("[jump]", merge.getLabels().toString());
		assertEquals(
				"{1=loc_loc1_loc1_loc1_(1), Invariant: x <= 5 & y <= 5 & z <= 5, Flow: x==4 & y==4 & z==4, IsForbidden?: false, "
						+ "2=loc_loc2_loc2_loc2_(2), Invariant: x <= 1000 & y<=1000 & z<=1000, Flow: , IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals("[(1) === (); {}; Label: jump ===> (2)]", merge.getTransitions().toString());
		estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
		/*
		 * Test 7, 3 automata with more than 2 locations, 1 sync transition in each
		 */
		System.out.println("Starting Test 7..");
		startTime = System.nanoTime();
		file = "../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test7.xml";
		fis = new FileInputStream(file);
		spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		system = new HybridModel(spaceEx, logger);
		merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y, z]", merge.getLocalParameters().toString());
		assertEquals("[jump]", merge.getLabels().toString());
		//@formatter:off
		assertEquals(
				"{1=loc_loc1_loc1_loc1_(1), Invariant: x <= 5 & y <= 5 & z <= 5, Flow: x==4 & y==4 & z==4, IsForbidden?: false, "
						+ "2=loc_loc2_loc2_loc2_(2), Invariant: x <= 1000 & y<=1000 & z<=1000, Flow: , IsForbidden?: false, "
						+ "3=loc_loc3_loc2_loc2_(3), Invariant: x <= 9999 & y<=1000 & z<=1000, Flow: , IsForbidden?: false, "
						+ "4=loc_loc4_loc2_loc2_(4), Invariant: x <= 5000 & y<=1000 & z<=1000, Flow: , IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals("[(1) === (); {}; Label: jump ===> (2), "
				+ "(2) === (); {} ===> (3), "
				+ "(2) === (); {} ===> (4)]",
				merge.getTransitions().toString());
		//@formatter:on
		estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
		/*
		 * Test 8, 3 automata with more than 2 locations, 2 sync transitions, Question: IS LOC 4 of aut1 unreachable?
		 */
		System.out.println("Starting Test 8..");
		startTime = System.nanoTime();
		file = "../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test8.xml";
		fis = new FileInputStream(file);
		spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		system = new HybridModel(spaceEx, logger);
		merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y, z]", merge.getLocalParameters().toString());
		assertEquals("[jump2, jump]", merge.getLabels().toString());
		//@formatter:off
		assertEquals(
				"{1=loc_loc1_loc1_loc1_(1), Invariant: x <= 5 & y <= 5 & z <= 5, Flow: x==4 & y==4 & z==4, IsForbidden?: false, "
						+ "2=loc_loc2_loc2_loc2_(2), Invariant: x <= 1000 & y<=1000 & z<=1000, Flow: , IsForbidden?: false, "
						+ "3=loc_loc3_loc3_loc2_(3), Invariant: x <= 9999 & y <= 9999 & z<=1000, Flow: , IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals("[(1) === (); {}; Label: jump ===> (2), "
				+ "(2) === (); {}; Label: jump2 ===> (3)]",
				merge.getTransitions().toString());
		//@formatter:on
		estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
		/*
		 * Test 9, 3 automata with more than 2 locations, loop
		 */
		System.out.println("Starting Test 9..");
		startTime = System.nanoTime();
		file = "../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test9.xml";
		fis = new FileInputStream(file);
		spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		system = new HybridModel(spaceEx, logger);
		merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y, z]", merge.getLocalParameters().toString());
		assertEquals("[jump]", merge.getLabels().toString());
		//@formatter:off
		assertEquals(
				"{1=loc_loc1_loc1_loc1_(1), Invariant: x <= 5 & y <= 5 & z <= 5, Flow: x==4 & y==4 & z==4, IsForbidden?: false, "
						+ "2=loc_loc2_loc2_loc2_(2), Invariant: x <= 1000 & y<=1000 & z<=1000, Flow: , IsForbidden?: false, "
						+ "3=loc_loc3_loc2_loc2_(3), Invariant: x <= 9999 & y<=1000 & z<=1000, Flow: , IsForbidden?: false, "
						+ "4=loc_loc4_loc2_loc2_(4), Invariant: x <= 5000 & y<=1000 & z<=1000, Flow: , IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals(
				"[(1) === (); {}; Label: jump ===> (2), "
				+ "(2) === (); {} ===> (3), "
				+ "(3) === (); {} ===> (4), "
				+ "(4) === (); {} ===> (2)]",
				merge.getTransitions().toString());
		//@formatter:on
		estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
		/*
		 * Test 10, 3 automata with more than 2 locations
		 */
		System.out.println("Starting Test 10..");
		startTime = System.nanoTime();
		file = "../SpaceExParserTest/src/de/uni_freiburg/informatik/ultimate/plugins/spaceex/automata/hybridsystem/testfiles/test10.xml";
		fis = new FileInputStream(file);
		spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		system = new HybridModel(spaceEx, logger);
		merge = system.mergeAutomata(system.getSystems().get("sys1"), null);
		System.out.println(merge);
		assertEquals("MERGE0", merge.getName());
		assertEquals("[]", merge.getGlobalConstants().toString());
		assertEquals("[]", merge.getGlobalParameters().toString());
		assertEquals("[]", merge.getLocalConstants().toString());
		assertEquals("[x, y, z]", merge.getLocalParameters().toString());
		assertEquals("[jump]", merge.getLabels().toString());
		//@formatter:off
		assertEquals(
				"{1=loc_loc1_loc1_loc1_(1), Invariant: x <= 5 & y <= 5 & z <= 5, Flow: x==4 & y==4 & z==4, IsForbidden?: false, "
						+ "2=loc_loc2_loc2_loc2_(2), Invariant: x <= 1000 & y<=1000 & z<=1000, Flow: , IsForbidden?: false, "
						+ "3=loc_loc3_loc2_loc2_(3), Invariant: x <= 9999 & y<=1000 & z<=1000, Flow: , IsForbidden?: false, "
						+ "4=loc_loc2_loc3_loc2_(4), Invariant: x <= 1000 & y <= 9999 & z<=1000, Flow: , IsForbidden?: false, "
						+ "5=loc_loc3_loc3_loc2_(5), Invariant: x <= 9999 & y <= 9999 & z<=1000, Flow: , IsForbidden?: false, "
						+ "6=loc_loc4_loc3_loc2_(6), Invariant: x <= 5000 & y <= 9999 & z<=1000, Flow: , IsForbidden?: false, "
						+ "7=loc_loc4_loc2_loc2_(7), Invariant: x <= 5000 & y<=1000 & z<=1000, Flow: , IsForbidden?: false}",
				merge.getLocations().toString());
		assertEquals(
				"[(1) === (); {}; Label: jump ===> (2), "
				+ "(2) === (); {} ===> (3), "
				+ "(2) === (y <= 9999); {} ===> (4), "
				+ "(4) === (); {} ===> (5), "
				+ "(5) === (x <= 5000); {} ===> (6), "
				+ "(3) === (x <= 5000 & y <= 9999); {} ===> (5), "
				+ "(3) === (x <= 5000); {} ===> (7), "
				+ "(7) === (y <= 9999); {} ===> (6)]",
				merge.getTransitions().toString());
		//@formatter:on
		estimatedTime = System.nanoTime() - startTime;
		System.out.println("Done in " + estimatedTime / (float) 1000000 + " milliseconds");
	}
	
}
