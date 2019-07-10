
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

/**
 * The class <code>J2UPPAALConverter</code> transforms a Phase Event automaton object into a xml-File that can be read
 * via UPPAAL. UPPAAL changed its input format since version 4.x. Thus use J2UPPAALWriter for UPPAAL versions below 4.x
 * and this Writer for version 4.x and ongoing.
 *
 * The algorithm bases on the one given by Jochen Hoenicke in "Combination of Processes, Data, and Time". 1) if the pea
 * has more than one initial state s0i, then we need to add a new initial state, with an edge to every s0i (as uppaal
 * allows only one initial state) 2) in the pea, if a state gets active, it has to be active for some time >0. Thus we
 * introduce a clock "timer". "Timer" is reset in every transition and every transition has a guard, that requires
 * "timer >0". 3) the edges are normalized such that each guard is a conjunct of literals. 4) for all edges (p,g,X,p')
 * of the pea: if s(p)&g&(s(p') is unsatisfiable remove this edge 5) remove unreachable locations 6) remove all literals
 * from the guard except clock constraints and set all state invariants to true 7) for all selfloops: if no clock is
 * reset on this selfloop, then remove this selfloop
 *
 * @author Amalinda Oertel April 2010
 *
 * @see J2UPPAALWriter
 */
public class J2UPPAALConverter {
	private final Vector<String> disjuncts = new Vector<>();
	private final String initialState = "initialState";
	protected int dnfCount = 1;
	protected int transCount = 0;
	protected BufferedWriter writer;

	// Amis TranistionCounter to count the number of transitions in the timed automaton
	private int transitionsInS = 0;
	private int transitionsInA = 0;
	String systemName = "System";

	// only needed for export measurement
	protected int deletedSelfloops = 0;
	protected int deletedTransitions = 0;

	public String[] getDisjuncts(final CDD cdd) {
		disjuncts.clear();
		// System.out.println("Computing dnf " + dnfCount + "/" + this.transCount +
		// "pea transitions");
		dnfCount++;
		cddToDNF(new StringBuffer(), cdd);

		final int disjunctCount = disjuncts.size();
		final String[] strings = new String[disjunctCount];

		for (int i = 0; i < disjunctCount; i++) {
			strings[i] = disjuncts.elementAt(i);
		}

		return strings;
	}

	private void cddToDNF(final StringBuffer buf, final CDD cdd) {
		if (cdd == CDD.TRUE) {
			// TODO fix this arghgrmbl implementation (presumably, complete
			// reimplementation needed)
			if (buf.toString().endsWith(" &amp;&amp; ")) {
				buf.delete(buf.length() - 12, buf.length());
			}

			// System.out.println("Adding="+buf.toString());
			disjuncts.add(buf.toString());

			return;
		} else if (cdd == CDD.FALSE) {
			return;
		}

		for (int i = 0; i < cdd.getChilds().length; i++) {
			final StringBuffer newBuf = new StringBuffer();
			newBuf.append(buf.toString());

			newBuf.append(cdd.getDecision().toUppaalString(i));
			newBuf.append(" &amp;&amp; ");

			cddToDNF(newBuf, cdd.getChilds()[i]);
		}
	}

	// Problem hier ist, dass auch die "falschen" Ergebnisse hochgegeben werden
	private StringBuffer cddToDNF_NEU(final StringBuffer buf, final CDD cdd) {
		if (cdd == CDD.TRUE) {
			if (buf.toString().endsWith(" &amp;&amp; ")) {
				buf.delete(buf.length() - 12, buf.length());
			}

			// System.out.println("Adding="+buf.toString());
			disjuncts.add(buf.toString());

			return buf;
		} else if (cdd == CDD.FALSE) {
			final StringBuffer emptyBuf = new StringBuffer();

			return emptyBuf;
		}

		final StringBuffer newBuf = new StringBuffer();

		for (int i = 0; i < cdd.getChilds().length; i++) {
			newBuf.append(buf.toString());
			newBuf.append(cdd.getDecision().toUppaalString(i));
			newBuf.append(XMLString.AND);
			cddToDNF(newBuf, cdd.getChilds()[i]);
		}

		return newBuf;
	}

	// Uppaal supports only one initial state; Thus, if a pea has more than one initial state,
	// we introduce a new state "initialState"
	private void addInitialStates(final PhaseEventAutomata pea) throws IOException {
		final Phase[] init = pea.getInit();

		// the following case should never occur if the pea was properly built, but you can never be sure...
		if (init.length <= 0) {
			System.out.println("ERROR: The pea has no init state");
		}

		// if the PEA has only one init state, then we do not need the further initialState
		if (init.length == 1) {
			writer.write("<init ref = \"" + init[0].getName() + "\"/>\n");
		} else // we need the further init state
		{
			// this further init state shall be committed, thus, there is no delay allowed in this state
			writer.write("<location id = \"" + initialState + "\">\n" + "  <name>" + initialState
					+ "</name>\n <committed/>\n </location>\n");
			// denote state as init state
			writer.write("<init ref = \"" + initialState + "\"/>\n");
		}
	}

	private String getClocksToReset(final Phase state, final List<String> peaClocks) {
		final String initClockString = state.getClockInvariant().toString();
		Boolean firstClock = true;

		// List<String> peaClocks = pea.getClocks();
		String reset = "";

		for (int j = 0; j < peaClocks.size(); j++) {
			if (initClockString.contains(peaClocks.get(j))) {
				if (firstClock) { // the end of the string may not end with a comma, otherwise uppaal will grump
					reset = peaClocks.get(j) + ":= 0";
					firstClock = false;
				} else {
					reset = reset + ", " + peaClocks.get(j) + ":= 0"; // the clocks need to be separated via comma
				}
			}
		}

		return reset;
	}

	private void addInitialTransitions(final PhaseEventAutomata pea) throws IOException {
		final Phase[] init = pea.getInit();
		final List<String> peaClocks = pea.getClocks();

		// if the PEA has only one init state, then we do not need the further initialState, and thus no further
		// transitions
		// otherwise add transitions from initialState to every init state and if this init state has a clock invariant
		// then reset the clock
		if (init.length > 1) {
			for (int i = 0; i < init.length; i++) { // for all init states

				final Phase initState = init[i];
				final CDD initClock = initState.getClockInvariant();

				// What clocks are part of the clock invariant of the initial state
				final String reset = getClocksToReset(initState, peaClocks);

				writer.write("<transition>\n" + "  <source ref = \"" + initialState + "\"/>\n" + "  <target ref = \""
						+ initState.getName() + "\"/>\n");

				transitionsInS++;

				// if the PEA inital state has a clock invariant, then we need to set the clock(s) to zero
				if (initClock != CDD.TRUE) {
					writer.write(" <label kind = \"assignment\">" + reset + "</label>\n");
				}

				writer.write("</transition>\n");
				writer.flush();
			}
		}
	}

	protected void addPEAStates(final Phase[] phases) throws IOException {
		for (int i = 0; i < phases.length; i++) {
			final Phase phase = phases[i];
			writer.write(
					"<location id = \"" + phase.getName() + "\"" + ">\n" + "  <name>" + phase.getName() + "</name>\n");

			if (phase.getClockInvariant() != CDD.TRUE) {
				final String[] formula2 = getDisjuncts(phase.getClockInvariant());
				writer.write("  <label kind = \"invariant\">" + formula2[0]);

				for (int j = 1; j < formula2.length; j++) {
					writer.write(XMLString.AND + formula2[j]);
				}

				writer.write("</label>\n");
			}

			writer.write("</location>\n");
		}
	}

	// add the transitions of the pea
	protected void addPEATransitions(final Phase[] phases) {
		final Vector<Transition> transitions = new Vector<>();

		for (int i = 0; i < phases.length; i++) {
			final Phase phase = phases[i];
			final List<Transition> transition = phase.getTransitions();
			transitionsInA = transitionsInA + transition.size();
			transitions.addAll(transition);
		}

		transCount = transitions.size();

		for (int j = 0; j < transCount; j++) {
			final Transition trans = transitions.elementAt(j);
			createPEATransitionString(trans);
		}
	}

	protected void createPEATransitionString(final Transition transition) {
		final String[] disjuncts = getDisjuncts(transition.getGuard());
		final String[] resets = transition.getResets();
		final StringBuffer assignment = new StringBuffer();

		for (int i = 0; i < resets.length; i++) {
			assignment.append(resets[i]).append(":=0, ");
		}

		assignment.append("timer:=0");

		for (int i = 0; i < disjuncts.length; i++) {
			final String source = transition.getSrc().getName();
			final String destination = transition.getDest().getName();

			if (source.matches(destination) && (resets.length <= 0)) {
				// selfloops in which no clock is reset do not need to be transfered to the uppaal model
				deletedSelfloops++; // only for measurement
			} else {
				// if s(p)&s(p')&g is unsatisfiable, delete this edge
				// CDD sourceInv = transition.getSrc().getStateInvariant();
				final CDD destInv = transition.getDest().getStateInvariant();
				final CDD guard = transition.getGuard();

				if (guard.and(destInv) == CDD.FALSE) {
					// do nothing
					deletedTransitions++;
				} else {
					try {
						writer.write("<transition>\n" + "  <source ref = \"" + source + "\"/>\n" + "  <target ref = \""
								+ destination + "\"/>\n");

						if (disjuncts[i].isEmpty()) {
							writer.write("  <label kind = \"guard\"> timer " + XMLString.GREATER + " 0 </label>\n");
						} else {
							writer.write("  <label kind = \"guard\">" + disjuncts[i] + XMLString.AND + "timer"
									+ XMLString.GREATER + "0 </label>\n");
						}

						writer.write("  <label kind = \"assignment\">" + assignment.toString() + "</label>\n"
								+ "</transition>\n");
						transitionsInS++;
						writer.flush();
					} catch (final IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
			}
		}
	}

	protected void createPEAString(final PhaseEventAutomata pea) throws IOException {
		final Phase[] phases = pea.getPhases();

		addPEAStates(phases);
		addInitialStates(pea);
		addInitialTransitions(pea);
		addPEATransitions(phases);
	}

	protected String addDeclarationOfClocks(final PhaseEventAutomata pea) {
		// we add a new clock "timer" to ensure that every state stays active for some time >0
		String clockDeclaration = "clock timer; ";

		// and (of course) we also add the clocks of the pea
		final int numberOfClocks = pea.getClocks().size();

		for (int i = 0; i < numberOfClocks; i++) {
			clockDeclaration = clockDeclaration + "clock " + pea.getClocks().get(i) + "; ";
		}

		return clockDeclaration;
	}

	public void writePEA2UppaalFile(final String file, final PhaseEventAutomata pea) {
		final long actTime = System.currentTimeMillis();

		try {
			writer = new BufferedWriter(new FileWriter(file));

			// FileWriter writer = new FileWriter(file);
			final String clockDeclaration = addDeclarationOfClocks(pea);

			// Uppaal does not accept system names that are too long --< we use only a short version of the name
			// int namelength = pea.getName().length();
			// String shortName = pea.getName();
			// if (namelength >= 15){
			// shortName = pea.getName().substring(0,15);
			// }
			final String shortName = systemName;

			// System.out.println(shortName);

			writer.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
					+ "<!DOCTYPE nta PUBLIC \"-//Uppaal Team//DTD Flat System 1.0//EN\" \"http://www.docs.uu.se/docs/rtmv/uppaal/xml/flat-1_0.dtd\"> \n"
					+ "<nta>\n" + "<declaration/>\n" + "<template>\n" + "<name>" + shortName + "</name>\n"
					+ "<declaration>" + clockDeclaration + "</declaration>\n");
			createPEAString(pea);
			writer.write("</template>\n" + "<system>system " + shortName + ";</system>\n" + "</nta>");
			writer.flush();
			writer.close();

			// System.out.println("System Name is: " + shortName);
		} catch (final Exception e) {
			System.out.println("Errors writing the Uppaal representation of pea");
			e.printStackTrace();
		}
		System.out.println("*****************************");
		System.out.println("Writing Uppaal representation took " + (System.currentTimeMillis() - actTime) + "ms");
		System.out.println("Computed " + (--dnfCount) + " disjunctive normalforms");
		System.out.println("Added: " + (pea.getInit().length) + " further transitions to initial states");
		System.out.println("Deleted: " + (deletedSelfloops) + " selfloops without clock reset");
		System.out.println("The Timed Automaton has " + (pea.getPhases().length) + " phases");
		System.out.println("The Timed Automaton has " + transitionsInS + " transitions");
		System.out.println("The PEA has " + transitionsInA + " transitions");
		System.out.println("*****************************");
	}

	public String getSystemName() {
		return systemName;
	}

	/**
	 * @param args
	 */
	public static void main(final String[] args) {
		// TODO Auto-generated method stub
	}

	// Wie in HTML m�ssen auch in XML Sonderzeichen speziell formatiert werden. Die Zeichen &, <, > sind:
	// & &amp;
	// < &lt;
	// > &gt;
	public static class XMLString {
		public static final String AND = " &amp;&amp; ";
		public static final String LESS = " &lt; ";
		public static final String LESSEQUAL = " &lt;= ";
		public static final String GREATER = " &gt; ";
		public static final String GREATEREQUAL = " &gt;= ";
	}
}
