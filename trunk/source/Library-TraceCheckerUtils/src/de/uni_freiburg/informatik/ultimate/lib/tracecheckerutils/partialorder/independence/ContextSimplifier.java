package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Context simplifier takes a trace, controlConfigurations and condition to simplify the trace and
 * controlConfigurations, where it only contains content that is relevant to the condition
 */
public class ContextSimplifier<L extends IAction> {

	private final Word<L> mLongTrace;
	private final List<?> mLongControlConfigurations;
	private final IPredicate mCondition;

	private List<Set<IProgramVar>> mAllRelevants;
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
		mAllRelevants = new ArrayList<>();

		// Set to keep track of relevant variables
		final Set<IProgramVar> relevant = new HashSet<>(mCondition.getVars());
		mAllRelevants.add(new HashSet<>(relevant));

		for (int i = mLongTrace.length() - 1; i >= 0; i--) {
			final Word<L> currentLetter = new Word<>(mLongTrace.getSymbol(i));

			// if no assignments are done, all sub statements of this statements are if or assume
			if (currentLetter.getSymbol(0).getTransformula().getAssignedVars().isEmpty()) {

				relevant.addAll(currentLetter.getSymbol(0).getTransformula().getInVars().keySet());
				mSimpleTrace = currentLetter.concatenate(mSimpleTrace);
				mTempControlConfigurations.add(mLongControlConfigurations.get(i + 1));
				mAllRelevants.add(new HashSet<>(relevant));
				continue;
			}

			// assert to ensure type casting always holds
			assert (currentLetter.getSymbol(0).getTransformula().getFormula() instanceof ApplicationTerm);

			if (currentLetter.getSymbol(0).getTransformula().getFormula() instanceof final ApplicationTerm formula) {
				// if mFormula.mFunction.mName is not "and", the statements consists of only one sub statements
				if (!"and".equals(formula.getFunction().getName())) {
					assert (currentLetter.getSymbol(0).getTransformula().getAssignedVars().size() == 1);
					final IProgramVar var =
							currentLetter.getSymbol(0).getTransformula().getAssignedVars().iterator().next();
					if (relevant.contains(var)) {
						// the only assigned variable is relevant
						mSimpleTrace = currentLetter.concatenate(mSimpleTrace);
						mTempControlConfigurations.add(mLongControlConfigurations.get(i + 1));
						relevant.remove(var);
						relevant.addAll(currentLetter.getSymbol(0).getTransformula().getInVars().keySet());
					}
					mAllRelevants.add(new HashSet<>(relevant));
					continue;
				}
				// the only not relevant variables, are variables in an assignment which is not relevant
				// if all mAssignedVars are in relevant, than all input variables are relevant
				if (relevant.containsAll(currentLetter.getSymbol(0).getTransformula().getAssignedVars())) {
					mSimpleTrace = currentLetter.concatenate(mSimpleTrace);
					mTempControlConfigurations.add(mLongControlConfigurations.get(i + 1));
					relevant.removeAll(currentLetter.getSymbol(0).getTransformula().getAssignedVars());
					relevant.addAll(currentLetter.getSymbol(0).getTransformula().getInVars().keySet());
					mAllRelevants.add(new HashSet<>(relevant));
					continue;
				}

				// for all relevant variables in mAssignedVars, we look at how they were computed and
				// add all corresponding input variables

				final Queue<TermVariable> queue = new ArrayDeque<>();
				final Set<TermVariable> lookedAt = new HashSet<>();

				for (final IProgramVar assignment : currentLetter.getSymbol(0).getTransformula().getAssignedVars()) {
					if (relevant.contains(assignment)) {
						relevant.remove(assignment);
						lookedAt.add(currentLetter.getSymbol(0).getTransformula().getOutVars().get(assignment));
						queue.offer(currentLetter.getSymbol(0).getTransformula().getOutVars().get(assignment));
					}
				}

				// if the amount of parameters (therefore sub statements) is different from mAssignedVars.size()
				// not all sub statements are assignments -> some are assume/if
				if (formula.getParameters().length != currentLetter.getSymbol(0).getTransformula().getAssignedVars()
						.size()) {
					for (final Term baseParameter : formula.getParameters()) {
						if (baseParameter instanceof final ApplicationTerm parameter
								&& !"=".equals(parameter.getFunction().getName())) {
							for (final TermVariable freeVariable : parameter.getFreeVars()) {
								if (!lookedAt.contains(freeVariable)) {
									lookedAt.add(freeVariable);
									queue.offer(freeVariable);
								}
							}
						}
					}
				}

				// if lookedAt is not Empty at least one assume/if or assignment to a relevant variable was done
				if (!lookedAt.isEmpty()) {
					mSimpleTrace = currentLetter.concatenate(mSimpleTrace);
					mTempControlConfigurations.add(mLongControlConfigurations.get(i + 1));
				}

				while (!queue.isEmpty()) {
					final TermVariable termVariable = queue.poll();
					boolean termVarInInput = false;
					for (final Map.Entry<IProgramVar, TermVariable> entry : currentLetter.getSymbol(0).getTransformula()
							.getInVars().entrySet()) {
						if (Objects.equals(entry.getValue(), termVariable)) {
							final IProgramVar computationTermVar = entry.getKey();
							if (computationTermVar != null) {
								relevant.add(computationTermVar);
								termVarInInput = true;
								break;
							}
						}
					}
					// if termVariable is an input, we don't need to look for its computation
					// and can skip to the next element
					if (termVarInInput) {
						continue;
					}

					// termVariable is not an input, we need to find all variables in its computation
					for (final Term baseParameter : formula.getParameters()) {
						if (baseParameter instanceof final ApplicationTerm parameter
								&& Arrays.asList(parameter.getFreeVars()).contains(termVariable)) {
							for (final TermVariable freeVariable : parameter.getFreeVars()) {
								if (!lookedAt.contains(freeVariable)) {
									lookedAt.add(freeVariable);
									queue.offer(freeVariable);
								}
							}
						}
					}
				}
				mAllRelevants.add(new HashSet<>(relevant));
			}
		}

		// the very first controlConfiguration is still missing
		mTempControlConfigurations.add(mLongControlConfigurations.get(0));
		Collections.reverse(mTempControlConfigurations);
		mSimpleControlConfigurations = mTempControlConfigurations;
		assert (mAllRelevants.get(0).equals(mCondition.getVars()));
		Collections.reverse(mAllRelevants);
		assert (mSimpleControlConfigurations.size() == mSimpleTrace.length() + 1);
		assert (mLongControlConfigurations.size() == mAllRelevants.size());

	}

	public Word<L> getSimpleTrace() {
		return mSimpleTrace;
	}

	public List<?> getSimpleControlConfigurations() {
		return mSimpleControlConfigurations;
	}

	public Word<L> getLongTrace() {
		return mLongTrace;
	}

	public List<?> getLongControlConfigurations() {
		return mLongControlConfigurations;
	}

	public IPredicate getCondition() {
		return mCondition;
	}

	public List<Set<IProgramVar>> getAllRelevants() {
		return mAllRelevants;
	}

}
