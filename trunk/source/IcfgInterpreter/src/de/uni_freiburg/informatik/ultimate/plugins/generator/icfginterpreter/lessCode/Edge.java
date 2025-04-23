package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;

public class Edge {
	private final Term mGuard;
	private final Update[] mUpdates;
	public final IcfgLocation mSource;
	public final IcfgLocation mTarget;

	public Edge(final Term guard, final Update[] updates, final IcfgLocation source, final IcfgLocation target) {
		mGuard = guard;
		mUpdates = updates;
		mSource = source;
		mTarget = target;
	}

	public HashMap<TermVariable, Value> update(final Map<TermVariable, Value> state, final NonDeterministicChoice ndc) {
		final HashMap<TermVariable, Value> out = new HashMap<>(state);

		for (final Update update : mUpdates) {
			out.put(update.getVariable(), update.makeValue(out, ndc));
		}

		return out;
	}

	public boolean guard(final Map<TermVariable, Value> state, final NonDeterministicChoice ndc) {
		return ((BoolValue) TermEvaluator.evaluate(state, mGuard, ndc)).getValue();
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();

		out.append("From ").append(mSource.toString()).append(" to ").append(mTarget.toString());
		out.append("\nGuard: ").append(mGuard.toStringDirect()).append("\n");
		if (mUpdates.length == 0) {
			out.append("No updates.");
		} else {
			out.append("Updates:");
		}
		for (final Update update : mUpdates) {
			out.append("\n").append(update.toString());
		}

		return out.toString();
	}

	public Term getGuardTerm() {
		return mGuard;
	}
}