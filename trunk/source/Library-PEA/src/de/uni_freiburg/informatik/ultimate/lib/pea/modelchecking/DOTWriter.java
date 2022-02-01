/**
 *
 */
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

/**
 * The class <code>DOTWriter</code> offers functionality to convert a Phase Event automaton object into a Dot-File. The
 * dot-file can then be visualized in Graphviz; Note that Graphviz cannot depict the math formulas(at least it cannot do
 * so under windows); However you can convert via dot2tex the dotfiles to texfiles (using the pgf-library) and get a
 * visualization via tex (including the math-formulas)
 *
 * For GraphViz see: http://www.graphviz.org/ For Dot2Tex see: http://www.fauskes.net/code/dot2tex/documentation/ For
 * PGF/TIK see: http://www.ctan.org/tex-archive/help/Catalogue/entries/pgf.html
 *
 * The Converter is called, e.g. with: // DOTWriter dotwriter = new DOTWriter("C:/Test.dot", ctParallel); //
 * dotwriter.write();
 *
 * @author Amalinda Oertel March 2010
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
 */
public class DOTWriter extends TCSWriter {

	public static class DOTString {
		public static final String DOT_NODEDEF_START = " [width=0.5pt, texlbl=\"$\\substack{";
		public static final String DOT_NODEDEF_END = " }$\"]; \n";
		public static final String TO = " -> ";
		public static final String STOP = ";";
		public static final String DOT_LABEL_START = " [label=\"                 \", width =1, texlbl=\"$\\substack{";
		public static final String DOT_LABEL_START1 = " [label=\" ";
		public static final String DOT_LABEL_START2 = " \", width =1, texlbl=\"$\\substack{";
		public static final String DOT_LABEL_END = "}$\"]; \n";

	}

	/**
	 * FileWriter to output file.
	 */
	protected FileWriter writer;
	protected boolean rename;
	protected PhaseEventAutomata pea2write;

	public DOTWriter(final String fileName, final PhaseEventAutomata pea) {
		super(fileName);
		pea2write = pea;
	}

	public DOTWriter(final String fileName) {
		super(fileName);
	}

	/**
	 * Constructor setting output file name and rename flag that indicates whether original location names have to be
	 * used or whether the locations are renamed into default names.
	 *
	 * @param file
	 * @param rename
	 */

	public DOTWriter(final String destfile, final boolean rename, final PhaseEventAutomata pea) {
		this(destfile, pea);
		this.rename = rename;
	}

	public void write(final String fileName, final PhaseEventAutomata pea) {
		try {
			pea2write = pea;
			writer = new FileWriter(fileName);
			// init();
			writePreamble();
			writeInitialTransitions();
			writeTransitions();
			writeClose();
			writer.flush();
			writer.close();
			System.out.println("Successfully written to " + fileName);
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}

	@Override
	public void write() {
		try {
			writer = new FileWriter(fileName);
			// init();
			writePreamble();
			writeInitialTransitions();
			writeTransitions();
			writeClose();
			writer.flush();
			writer.close();
			System.out.println("Successfully written to " + fileName);
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}

	@Override
	protected void writeAndDelimiter(final Writer writer) throws IOException {
		// TODO Auto-generated method stub

	}

	@Override
	protected void writeDecision(final Decision decision, final int child, final Writer writer) throws IOException {
		// TODO Auto-generated method stub

	}

	protected void writePreamble() throws IOException {
		writer.write("/* Preamble:\n" + " File automatically generated via DOTWriter\n\n */" + " digraph G { \n");
	}

	/**
	 * instead of initial edges we construct a new initial node "init" and write edges to the initial nodes
	 *
	 * As Tex interprets "_" as command, we need to delete(or change) it from the names of the states.
	 *
	 * @throws IOException
	 *             thrown if writing of output file fails
	 */
	protected void writeInitialTransitions() throws IOException {

		final Phase[] init = pea2write.getInit();
		for (int i = 0; i < init.length; i++) {
			String initState = init[i].toString();
			initState = initState.replace("_", "");
			writer.write("null" + initState + " [shape = plaintext label=\"\"] \n");
			writer.write("null" + initState + DOTString.TO + initState + DOTString.STOP + "\n");
			// this.writer.write("init "+ DOTString.TO + initState + DOTString.STOP + "\n");

			// \node[initial,state] (A) {$q_a$};

		}
	}

	protected void writeClose() throws IOException {
		writer.write("\n }");
	}

	/**
	 * To get the edge labels more readable I'm using \substack and \\\\ for new lines As Tex interprets "_" as command,
	 * we need to delete(or change) it from the names of the states.
	 */
	protected void writeTransitions() throws IOException {
		final Phase[] phases = pea2write.getPhases();

		for (int i = 0; i < phases.length; i++) {
			final Phase currentPhase = phases[i];
			String location = currentPhase.getName();
			location = location.replace("_", "");
			String clock = currentPhase.getClockInvariant().toTexString();
			clock = clock.replace("_", "");
			String predicate = currentPhase.getStateInvariant().toTexString();
			predicate = predicate.replace("\\wedge", "\\wedge \\\\");
			predicate = predicate.replace("\\vee", "\\vee \\\\");
			predicate = predicate.replace("_", "");
			writer.write(location + DOTString.DOT_NODEDEF_START + location + " \\\\ " + predicate + " \\\\ " + clock
					+ DOTString.DOT_NODEDEF_END);

			final List<Transition> transitions = currentPhase.getTransitions();
			final Iterator it = transitions.iterator();
			while (it.hasNext()) {
				final Transition t = (Transition) it.next();
				String start = t.getSrc().getName();
				start = start.replace("_", "");
				String end = t.getDest().getName();
				end = end.replace("_", "");
				String guard = t.getGuard().toTexString();
				guard = guard.replace("_", "");
				guard = guard.replace("\\wedge", "\\wedge \\\\");
				final String[] reset = t.getResets();

				String guard2 = " ";
				for (int j = guard.length(); j > 0; j--) {
					guard2 = guard2.concat(" ");
				}

				String result = " ";
				if (reset.length > 0) {
					for (int j = 0; j < reset.length; j++) {
						result = result + reset[j] + " := 0 ";
					}
				}
				result = result.replace("_", "");

				writer.write(" " + start + DOTString.TO + end + DOTString.DOT_LABEL_START1 + guard2
						+ DOTString.DOT_LABEL_START2 + guard + " \\\\ " + result + DOTString.DOT_LABEL_END);

			}
		}
	}
}
