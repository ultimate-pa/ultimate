package de.uni_freiburg.informatik.ultimate.witnessprinter.yaml;

import java.time.OffsetDateTime;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Invariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Metadata;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Producer;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Task;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;
import de.uni_freiburg.informatik.ultimate.witnessprinter.preferences.PreferenceInitializer;

public class YamlCorrectnessWitnessGenerator {
	private static final String[] ACSL_SUBSTRING = new String[] { "\\old", "\\result", "\\exists" };

	private final ILogger mLogger;
	private final IBacktranslatedCFG<?, ?> mTranslatedCFG;
	private final boolean mIsACSLForbidden;
	private final IPreferenceProvider mPreferences;

	public YamlCorrectnessWitnessGenerator(final IBacktranslatedCFG<?, ?> translatedCFG, final ILogger logger,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mTranslatedCFG = translatedCFG;
		mPreferences = PreferenceInitializer.getPreferences(services);
		mIsACSLForbidden = mPreferences.getBoolean(PreferenceInitializer.LABEL_DO_NOT_USE_ACSL);
	}

	public String makeYamlString() {
		final var roots = mTranslatedCFG.getCFGs();
		if (roots.size() != 1) {
			throw new UnsupportedOperationException("Cannot generate correctness witnesses in library mode");
		}
		final var root = roots.get(0);
		final Deque<IExplicitEdgesMultigraph<?, ?, ?, ?, ?>> worklist = new ArrayDeque<>();

		final Set<IExplicitEdgesMultigraph<?, ?, ?, ?, ?>> closed = new HashSet<>();
		worklist.add(root);

		final String producer = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER);
		final String hash = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PROGRAMHASH);
		final String spec = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_SPECIFICATION);
		final String arch = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_ARCHITECTURE);
		final String version = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER_VERSION);
		final String format = mIsACSLForbidden ? "C" : "ACSL";
		final String filename = mTranslatedCFG.getFilename();
		// TODO: Do not hardcode FormatVersion
		final Supplier<Metadata> metadataSupplier = () -> new Metadata(new FormatVersion(0, 1), UUID.randomUUID(),
				OffsetDateTime.now(), new Producer(producer, version),
				new Task(List.of(filename), Map.of(filename, hash), spec, arch, "C"));

		final List<WitnessEntry> entries = new ArrayList<>();
		while (!worklist.isEmpty()) {
			final IExplicitEdgesMultigraph<?, ?, ?, ?, ?> node = worklist.remove();
			if (!closed.add(node)) {
				continue;
			}
			final Set<Location> locationCandidates = new HashSet<>();
			for (final var outgoing : node.getOutgoingEdges()) {
				final ILocation loc = (ILocation) outgoing.getLabel();
				// If the column is unknown (-1), use the first position of the line
				final int column = Math.max(loc.getStartColumn(), 0);
				// TODO: Where do we get the function from?
				locationCandidates.add(new Location(loc.getFileName(), hash, loc.getStartLine(), column, "function"));
				worklist.add(outgoing.getTarget());
			}
			final String invariant = filterInvariant(node);
			// TODO: Can we do anything if there are multiple locationCandidates?
			if (invariant != null && locationCandidates.size() == 1) {
				// TODO: How could we figure out, if it is a LocationInvariant or LoopInvariant?
				// For now we only produce loop invariants anyways
				entries.add(new LoopInvariant(metadataSupplier.get(), locationCandidates.iterator().next(),
						new Invariant(invariant, "assertion", format)));
			}
		}
		return new Witness(entries).toYamlString();
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
