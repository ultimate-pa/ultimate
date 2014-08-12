package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.utils;

import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

public class Utils {
	public static String insertLineBreaks(int chopSize, String s) {
		if (s.length() < chopSize) {
			return s;
		} else {
			int chops = s.length() / chopSize;
			int currentChopSize = chopSize;
			int possibleChopPoint = 0;
			int oldPossibleChopPoint = 0;
			while (chops > 0) {

				possibleChopPoint = s.indexOf(";", oldPossibleChopPoint);
				if (possibleChopPoint > currentChopSize) {
					s = s.substring(0, oldPossibleChopPoint).concat("\n")
							.concat(s.substring(oldPossibleChopPoint));
					--chops;
					currentChopSize = currentChopSize + chopSize;
				}
				oldPossibleChopPoint = possibleChopPoint + 1;

				if (possibleChopPoint > s.length() || possibleChopPoint == -1) {
					break;
				}

			}
			return "\n" + s;
		}

	}

	public static String traceToString(List<RCFGEdge> trace) {
		StringBuilder sb = new StringBuilder();
		for (RCFGEdge edge : trace) {
			sb.append(edgeToString(edge));
			sb.append(" ");
		}
		return sb.toString();
	}

	public static String edgeToString(RCFGEdge edge) {
		if (edge instanceof CodeBlock) {
			return ((CodeBlock) edge).getPrettyPrintedStatements();
		} else {
			return edge.toString();
		}
	}

	public static <T> HashSet<T> intersect(HashSet<T> a, HashSet<T> b) {
		HashSet<T> rtr = new HashSet<>();
		for (T element : a) {
			if (b.contains(element)) {
				rtr.add(element);
			}
		}
		return rtr;
	}

}
