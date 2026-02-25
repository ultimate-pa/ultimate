package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Context simplifier takes a trace, controlConfigurations and condition to simplify the trace and
 * controlConfigurations, where it only contains content that is relevant to the condition
 */
public class ContextSimplifier<L extends IAction> {

	public final Word<L> mLongTrace;
	public final List<?> mLongControlConfigurations;
	public final IPredicate mCondition;

	private Word<L> mSimpleTrace;
	private List<?> mSimpleControlConfigurations;

	public ContextSimplifier(final Word<L> longTrace, final List<?> longControlConfigurations,
			final IPredicate condition) {
		mLongTrace = longTrace;
		mLongControlConfigurations = longControlConfigurations;
		mCondition = condition;

		simplifyContext();
	}

	private void simplifyContext() {
		assert (mLongControlConfigurations.size() == mLongTrace.length() + 1);

		mSimpleTrace = new Word<>();

		// because java doesn't allow to add to <?> Lists together
		final List<Object> mTempControlConfigurations = new ArrayList<>();

		// Set to keep track of relevant variables
		final Set<IProgramVar> relevant = new HashSet<>(mCondition.getVars());
		for (int i = mLongTrace.length() - 1; i >= 0; i--) {
			final Word<L> currentLetter = new Word<>(mLongTrace.getSymbol(i));
			for (final IProgramVar var : currentLetter.getSymbol(0).getTransformula().getAssignedVars()) {
				if (relevant.contains(var)) {
					// a relevant variable is changed, therefore the statement is relevant
					// it is added by concatenating at the front
					mSimpleTrace = currentLetter.concatenate(mSimpleTrace);
					mTempControlConfigurations.add(0, mLongControlConfigurations.get(i + 1));

					// update relevant variables by adding all input variables
					relevant.remove(var);
					relevant.addAll(currentLetter.getSymbol(0).getTransformula().getInVars().keySet());
					break;
				}
			}
		}
		// the very first controlConfiguration is still missing
		mTempControlConfigurations.add(0, mLongControlConfigurations.get(0));
		mSimpleControlConfigurations = mTempControlConfigurations;
		assert (mSimpleControlConfigurations.size() == mSimpleTrace.length() + 1);
	}

	public Word<L> getSimpleTrace() {
		return mSimpleTrace;
	}

	public List<?> getSimpleControlConfigurations() {
		return mSimpleControlConfigurations;
	}

}
