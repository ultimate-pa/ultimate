package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

public class DotWriterNew {

	public static String node(final String nodeId, final String attrList) {
		String result = "";

		result += nodeId + " [label=\"" + attrList + "\"];" + "\n";

		return result;
	}

	public static void write(final String fileName, final boolean rename, final PhaseEventAutomata pea,
			final ILogger logger) throws IOException {

		String dot = "";

		dot += "digraph G {" + "\n\n";
		dot += "rankdir=LR;" + "\n";
		dot += "graph [fontname=\"arial\"]";
		dot += "node [fontname=\"arial\" shape=circle];" + "\n";
		dot += "edge [fontname=\"arial\"]";
		dot += "\n";

		for (final Phase phase : pea.getInit()) {
			final String location = phase.getName();

			dot += "_" + location + " [style=invis];" + "\n";
			dot += "\t" + "_" + location + " -> " + location + ";" + "\n";
			dot += "\n";
		}

		for (final Phase phase : pea.getPhases()) {
			final String location = phase.getName();
			final String clock = phase.getClockInvariant().toUppaalString();
			final String predicate = phase.getStateInvariant().toUppaalString();

			String table = "";
			table += "<<b>" + location + "</b><br/>";
			table += "<font COLOR=\"#984ea3\">" + predicate + "</font><br/>";
			table += "<font COLOR=\"#ff7f00\">" + clock + "</font><br/>>";

			// dot += location + " [label=\"" + location + "\\n" + predicate + "\\n" + clock + "\"];" + "\n";
			dot += location + " [label=" + table + "];" + "\n";

			for (final Transition transition : phase.getTransitions()) {
				final String src = transition.getSrc().getName();
				final String dst = transition.getDest().getName();
				final String guard = transition.getGuard().toUppaalString();

				String resets = "";
				for (final String reset : transition.getResets()) {
					resets += "<br/>" + reset + " :=0";
				}

				dot += "\t" + src + " -> " + dst + " [label=" + "<<br/><font COLOR=\"#377eb8\">" + guard + "</font>"
						+ resets + ">];" + "\n";
			}
			dot += "\n";
		}
		dot += "}";

		final List<String> clocks = pea.getClocks();
		for (int i = 0; i < clocks.size(); i++) {
			dot = dot.replaceAll(clocks.get(i), "c" + String.valueOf(i));
		}

		final FileWriter writer = new FileWriter(fileName);
		writer.write(dot);
		writer.close();
	}
}
