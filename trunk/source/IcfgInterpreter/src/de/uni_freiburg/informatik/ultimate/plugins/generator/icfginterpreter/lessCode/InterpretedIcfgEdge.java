package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;

public class InterpretedIcfgEdge {
	private final Term mGuard;
	private final Set<PossibleUpdate> mUpdates;
	private final IcfgEdge mEdge;

	public InterpretedIcfgEdge(final Term guard, final Set<PossibleUpdate> updateVariants, final IcfgEdge edge) {
		mGuard = guard;
		mUpdates = updateVariants;
		mEdge = edge;
	}

	public record PossibleUpdate(Term guard, Update[] updates) {
		public boolean guard(final Map<Term, Value> state, final NonDeterministicChoice ndc) {
			return ((BoolValue) TermEvaluator.evaluate(state, guard, ndc)).getValue();
		}

		public HashMap<Term, Value> update(final Map<Term, Value> state, final NonDeterministicChoice ndc) {
			final HashMap<Term, Value> out = new HashMap<>(state);

			for (final Update update : updates) {
				out.put(update.getVariable(), update.makeValue(out, ndc));
			}

			return out;
		}
	}

	public IcfgLocation getTarget() {
		return mEdge.getTarget();
	}

	public IcfgLocation getSource() {
		return mEdge.getSource();
	}

	public IcfgEdge getEdge() {
		return mEdge;
	}

	public HashMap<Term, Value> update(final Map<Term, Value> state, final NonDeterministicChoice ndc) {
		final HashMap<Term, Value> out = new HashMap<>(state);

		for (final PossibleUpdate update : mUpdates) {
			if (update.guard(state, ndc)) {
				// TODO return all new states if more than one possible
				return update.update(state, ndc);
			}
		}

		return out;
	}

	public boolean guard(final Map<Term, Value> state, final NonDeterministicChoice ndc) {
		return ((BoolValue) TermEvaluator.evaluate(state, mGuard, ndc)).getValue();
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();

		out.append("From ").append(getSource().toString()).append(" to ").append(getTarget().toString());
		out.append("\nGuard: ").append(mGuard.toStringDirect());
		if (mUpdates.size() == 0) {
			out.append("\nNo updates.");
		}
		for (final PossibleUpdate updateSet : mUpdates) {
			out.append("\nSubguard:");
			out.append("\n\t").append(updateSet.guard.toStringDirect());
			out.append("\nUpdates:");
			for (final Update update : updateSet.updates) {
				out.append("\n\t").append(update.toString());
			}
		}

		return out.toString();
	}

	public Term getGuardTerm() {
		return mGuard;
	}
}