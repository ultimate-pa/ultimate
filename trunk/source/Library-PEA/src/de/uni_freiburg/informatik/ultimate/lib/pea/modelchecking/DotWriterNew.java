package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.util.List;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

public class DotWriterNew {

	public static StringBuilder createDotString(final PhaseEventAutomata pea) {
		StringBuilder rtr = new StringBuilder();

		rtr.append("digraph G {" + "\n\n");
		rtr.append("rankdir=LR;" + "\n");
		rtr.append("graph [fontname=\"arial\"]" + "\n");
		rtr.append("node [fontname=\"arial\" shape=circle];" + "\n");
		rtr.append("edge [fontname=\"arial\"]");
		rtr.append("\n");

		for (final Phase phase : pea.getInit()) {
			final String location = phase.getName();

			rtr.append("_" + location + " [style=invis];" + "\n");
			rtr.append("\t" + "_" + location + " -> " + location + ";" + "\n");
			rtr.append("\n");
		}

		for (final Phase phase : pea.getPhases()) {
			final String location = phase.getName();
			final String predicate = phase.getStateInvariant().toUppaalString();
			final String clock = phase.getClockInvariant().toUppaalString();

			String label = "<<b>" + location + "</b><br/>";
			label += "<font COLOR=\"#984ea3\">" + predicate + "</font><br/>";
			label += "<font COLOR=\"#ff7f00\">" + clock + "</font><br/>>";

			rtr.append(location + " [label=" + label + "];" + "\n");

			for (final Transition transition : phase.getTransitions()) {
				final String src = transition.getSrc().getName();
				final String dst = transition.getDest().getName();
				final String guard = transition.getGuard().toUppaalString();

				String resets = "";
				for (final String reset : transition.getResets()) {
					resets += "<br/>" + reset + " :=0";
				}

				rtr.append("\t" + src + " -> " + dst + " [label=" + "<<br/><font COLOR=\"#377eb8\">" + guard + "</font>"
						+ resets + ">];" + "\n");
			}
			rtr.append("\n");
		}
		rtr.append("}");

		final List<String> clocks = pea.getClocks();
		for (int i = 0; i < clocks.size(); i++) {
			rtr = new StringBuilder(Pattern.compile(clocks.get(i)).matcher(rtr).replaceAll("c" + String.valueOf(i)));
		}

		return rtr;
	}
}
