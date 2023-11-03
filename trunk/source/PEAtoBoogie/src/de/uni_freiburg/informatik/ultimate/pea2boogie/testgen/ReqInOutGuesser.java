package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;

public class ReqInOutGuesser {

	private final ILogger mLogger;
	private final Map<String, DeclarationPattern> mVar2InitPattern;
	private final List<DeclarationPattern> mNewInitPatterns;
	private final Map<String, Integer> mId2Bounds;
	private final List<PatternType<?>> mNewRequirements;
	private final Set<PatternType<?>> mRequirementsWithTransformationErrors;
	private final PeaResultUtil mResultUtil;

	public ReqInOutGuesser(final ILogger logger, final IUltimateServiceProvider services,
			final List<DeclarationPattern> oldInitPatterns, final List<PatternType<?>> reqPatterns) {
		mLogger = logger;
		mVar2InitPattern = new HashMap<>();
		mId2Bounds = new HashMap<>();
		mResultUtil = new PeaResultUtil(logger, services);

		mRequirementsWithTransformationErrors = new HashSet<>();

		final Set<DeclarationPattern> constInitPatterns = new HashSet<>();
		for (final DeclarationPattern p : oldInitPatterns) {
			if (p.getCategory() == VariableCategory.CONST) {
				// we do not care for the concrete value, but only for something we can build countertraces with
				mId2Bounds.put(p.getId(), 42);
				constInitPatterns.add(p);
			} else {
				mVar2InitPattern.put(p.getId(), p);
			}
		}
		if (isInputOnlyPattern(oldInitPatterns)) {
			// TODO: What about overwrite existing assignment?
			mLogger.warn("No input/output assignment was chosen! We will make a very conservative guess.");
			mNewInitPatterns = generateNewInitializationPattern(mVar2InitPattern.values(), reqPatterns);
			mNewInitPatterns.addAll(constInitPatterns);
		} else {
			mNewInitPatterns = oldInitPatterns;
		}
		if (mRequirementsWithTransformationErrors.isEmpty()) {
			mNewRequirements = reqPatterns;
		} else {
			mNewRequirements = new ArrayList<>(reqPatterns.size());
			for (final PatternType<?> pattern : reqPatterns) {
				if (mRequirementsWithTransformationErrors.contains(pattern)) {
					continue;
				}
				mNewRequirements.add(pattern);
			}
		}
	}

	private List<DeclarationPattern> generateNewInitializationPattern(
			final Collection<DeclarationPattern> oldInitPatterns, final List<PatternType<?>> reqPatterns) {
		final Set<String> allVars = getAllVariables(oldInitPatterns);
		final Set<String> effectVars = getEffectVariables(reqPatterns);
		final Set<String> precondVars = getPreconditionVars(reqPatterns);
		// every variable, that is never influenced by a requirement has to be an input var
		final Set<String> inputVars = new HashSet<>(allVars);
		inputVars.removeAll(effectVars);
		mLogger.warn("Inputs: " + inputVars.toString());
		// output vars are all that are never used in a precondition
		final Set<String> outputVars = new HashSet<>(allVars);
		outputVars.removeAll(precondVars);
		mLogger.warn("Outputs: " + outputVars.toString());
		// calculate remaining vars for easy generation of init things
		final Set<String> remainingVars = new HashSet<>(allVars);
		remainingVars.removeAll(inputVars);
		remainingVars.removeAll(outputVars);
		// generate new pattern
		final List<DeclarationPattern> newInitPattern = new ArrayList<>();
		for (final String var : inputVars) {
			newInitPattern
					.add(new DeclarationPattern(var, mVar2InitPattern.get(var).getType(), VariableCategory.IN));
		}
		for (final String var : outputVars) {
			newInitPattern
					.add(new DeclarationPattern(var, mVar2InitPattern.get(var).getType(), VariableCategory.OUT));
		}
		for (final String var : remainingVars) {
			newInitPattern
					.add(new DeclarationPattern(var, mVar2InitPattern.get(var).getType(), VariableCategory.HIDDEN));
		}
		return newInitPattern;
	}

	private Set<String> getEffectVariables(final List<PatternType<?>> oldPatterns) {
		final Set<String> effectVars = new HashSet<>();
		for (final PatternType<?> pattern : oldPatterns) {
			effectVars.addAll(reportTransformationErrorWrapper(Req2CauseTrackingCDD::getEffectVariables, pattern));
		}
		return effectVars;
	}

	private Set<String> getPreconditionVars(final List<PatternType<?>> oldPatterns) {
		final Set<String> precondVars = new HashSet<>();
		for (final PatternType<?> pattern : oldPatterns) {
			final Set<String> vars = reportTransformationErrorWrapper(Req2CauseTrackingCDD::getAllVariables, pattern);
			vars.removeAll(reportTransformationErrorWrapper(Req2CauseTrackingCDD::getEffectVariables, pattern));
			precondVars.addAll(vars);
		}
		return precondVars;
	}

	private Set<String> reportTransformationErrorWrapper(final Function<PatternType<?>, Set<String>> fun,
			final PatternType<?> pattern) {
		if (mRequirementsWithTransformationErrors.contains(pattern)) {
			// already broken
			return Collections.emptySet();
		}
		try {
			return fun.apply(pattern);
		} catch (final Exception ex) {
			final String reason = ex.getMessage() == null ? ex.getClass().toString() : ex.getMessage();
			mResultUtil.transformationError(pattern, reason);
			mRequirementsWithTransformationErrors.add(pattern);
			return Collections.emptySet();
		}
	}

	private static Set<String> getAllVariables(final Collection<DeclarationPattern> oldPatterns) {
		final Set<String> effectVars = new HashSet<>();
		for (final PatternType<?> pattern : oldPatterns) {
			effectVars.add(((DeclarationPattern) pattern).getId());
		}
		return effectVars;
	}

	private static boolean isInputOnlyPattern(final List<DeclarationPattern> initPattern) {
		for (final DeclarationPattern p : initPattern) {
			if (p.getCategory() != VariableCategory.IN && p.getCategory() != VariableCategory.CONST) {
				return false;
			}
		}
		return true;
	}

	public List<DeclarationPattern> getInitializationPatterns() {
		return mNewInitPatterns;
	}

	/**
	 * @return valid non-initialization patterns (aka "real" requirements)
	 */
	public List<PatternType<?>> getRequirements() {
		return mNewRequirements;
	}

}
