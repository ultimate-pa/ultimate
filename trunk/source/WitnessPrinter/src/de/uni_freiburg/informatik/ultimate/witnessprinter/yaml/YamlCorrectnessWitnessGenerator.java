package de.uni_freiburg.informatik.ultimate.witnessprinter.yaml;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Invariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;
import de.uni_freiburg.informatik.ultimate.witnessprinter.preferences.PreferenceInitializer;

public class YamlCorrectnessWitnessGenerator {
	private static final String[] ACSL_SUBSTRING = new String[] { "\\old", "\\result", "\\exists" };

	private final ILogger mLogger;
	private final IBacktranslatedCFG<?, ?> mTranslatedCFG;
	private final boolean mIsACSLForbidden;

	public YamlCorrectnessWitnessGenerator(final IBacktranslatedCFG<?, ?> translatedCFG, final ILogger logger,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mTranslatedCFG = translatedCFG;
		mIsACSLForbidden =
				PreferenceInitializer.getPreferences(services).getBoolean(PreferenceInitializer.LABEL_DO_NOT_USE_ACSL);
	}

	private Witness getWitness() {
		final var roots = mTranslatedCFG.getCFGs();
		if (roots.size() != 1) {
			throw new UnsupportedOperationException("Cannot generate correctness witnesses in library mode");
		}
		final var root = roots.get(0);
		final Deque<IExplicitEdgesMultigraph<?, ?, ?, ?, ?>> worklist = new ArrayDeque<>();

		final Set<IExplicitEdgesMultigraph<?, ?, ?, ?, ?>> closed = new HashSet<>();
		worklist.add(root);

		final List<WitnessEntry> entries = new ArrayList<>();
		while (!worklist.isEmpty()) {
			final IExplicitEdgesMultigraph<?, ?, ?, ?, ?> node = worklist.remove();
			if (!closed.add(node)) {
				continue;
			}
			final Set<Location> locationCandidates = new HashSet<>();
			for (final var outgoing : node.getOutgoingEdges()) {
				// TODO: Can we use type constraints instead of this cast?
				final ILocation loc = (ILocation) outgoing.getLabel();
				locationCandidates.add(
						new Location(loc.getFileName(), "hash", loc.getStartLine(), loc.getStartColumn(), "function"));
				worklist.add(outgoing.getTarget());
			}
			final String invariant = filterInvariant(node);
			// TODO: Can we do anything if there are multiple locationCandidates?
			if (invariant != null && locationCandidates.size() == 1) {
				// TODO: How could we figure out, if it is a LocationInvariant or LoopInvariant?
				entries.add(new LocationInvariant(null, locationCandidates.iterator().next(),
						new Invariant(invariant, "assertion", "C")));
			}
		}
		return new Witness(entries);
	}

	public String makeYamlString() {
		return getWitness().toYamlString();
	}

	private String filterInvariant(final IExplicitEdgesMultigraph<?, ?, ?, ?, ?> node) {
		if (node == null) {
			return null;
		}
		if (node.getLabel() == null) {
			return null;
		}
		final String label = node.getLabel().toString();
		if (mIsACSLForbidden && label != null && Arrays.stream(ACSL_SUBSTRING).anyMatch(label::contains)) {
			mLogger.warn("Not writing invariant because ACSL is forbidden: " + label);
			return null;
		}
		return label;
	}
}
