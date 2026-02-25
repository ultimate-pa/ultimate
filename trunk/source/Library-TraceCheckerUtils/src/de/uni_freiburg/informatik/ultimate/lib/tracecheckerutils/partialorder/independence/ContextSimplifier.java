package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
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

					// where all input variables become relevant:
					// relevant.addAll(currentLetter.getSymbol(0).getTransformula().getInVars().keySet());

					/*
					 * for atomics where only one code line is relevant and only variables in the computation become
					 * relevant by: in mOutVars we look up to what TermVariable var is set, we call this value then for
					 * value we look up which other TermVariables were in its computation in mParameters and for all
					 * these TermVariables we look up their variable in mInVars
					 */

					final TermVariable value = currentLetter.getSymbol(0).getTransformula().getOutVars().get(var);
					if (value != null) {

						// all the type casts are because getter only exist for subclasses of Term
						final Term currentFormula = currentLetter.getSymbol(0).getTransformula().getFormula();
						if (currentFormula instanceof final ApplicationTerm appTerm) {
							for (final Term parameter : appTerm.getParameters()) {
								if ((parameter instanceof final ApplicationTerm relevantParameter)
										&& Arrays.asList(relevantParameter.getFreeVars()).contains(value)) {
									for (final TermVariable termVar : relevantParameter.getFreeVars()) {
										if (termVar != value) {
											for (final Map.Entry<IProgramVar, TermVariable> entry : currentLetter
													.getSymbol(0).getTransformula().getInVars().entrySet()) {
												if (Objects.equals(entry.getValue(), termVar)) {
													final IProgramVar computationTermVar = entry.getKey();
													if (computationTermVar != null) {
														relevant.add(computationTermVar);
													}
												}
											}
										}
									}
								}
							}
						}
					}
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
