package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.util.Formatter;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

/**
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class DotWriterNew {

	private static final String LINE_SEP = System.lineSeparator();

	/*
	 * Create dot string for a given {@link PhaseEventAutomata}.
	 */
	public static String createDotString(final PhaseEventAutomata<CDD> pea) {
		final StringBuilder stringBuilder = new StringBuilder();
		final Formatter fmt = new Formatter(stringBuilder);

		fmt.format("digraph G {%s", LINE_SEP);
		fmt.format("rankdir=LR;%s", LINE_SEP);
		fmt.format("graph [fontname=\"arial\"]%s", LINE_SEP);
		fmt.format("node [fontname=\"arial\" shape=rectangle];%s", LINE_SEP);
		fmt.format("edge [fontname=\"arial\"]%s", LINE_SEP);

		for (final Phase<CDD> phase : pea.getInit()) {
			final String location = phase.getName();

			fmt.format("_%s [style=invis];%s", location, LINE_SEP);
			fmt.format("\t_%s -> %s;%s%s", location, location, LINE_SEP, LINE_SEP);
		}

		for (final Phase<CDD> phase : pea.getPhases()) {
			final String location = phase.getName();
			final String predicate = phase.getStateInvariant().toUppaalString();
			final String clock = phase.getClockInvariant().toUppaalString();

			String label = "<<b>" + location + "</b><br/>";
			label += "<font COLOR=\"#984ea3\">" + predicate + "</font><br/>";
			label += "<font COLOR=\"#ff7f00\">" + clock + "</font><br/>>";

			fmt.format("%s [label=%s];%s", location, label, LINE_SEP);

			for (final Transition<CDD> transition : phase.getTransitions()) {
				final String src = transition.getSrc().getName();
				final String dst = transition.getDest().getName();
				final String guard = transition.getGuard().toUppaalString();

				String resets = "";
				for (final String reset : transition.getResets()) {
					resets += "<br/>" + reset + " :=0";
				}

				fmt.format("\t%s -> %s [label=<<font COLOR=\"#377eb8\">%s</font>%s>];%s", src, dst, guard, resets,
						LINE_SEP);
			}
			fmt.format("%s", LINE_SEP);
		}
		fmt.format("}");
		fmt.close();

		// Replace clock names by names of the form c[0-9].
		String string = stringBuilder.toString();
		final AtomicInteger counter = new AtomicInteger(0);
		for (final String clock : pea.getClocks()) {
			string = string.replaceAll(clock, "c" + String.valueOf(counter.getAndIncrement()));
		}

		return string;
	}
}
