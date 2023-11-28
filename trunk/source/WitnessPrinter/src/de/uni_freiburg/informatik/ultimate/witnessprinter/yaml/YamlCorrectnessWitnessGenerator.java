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

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
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
	private static final String[] ACSL_SUBSTRING = new String[] { "\\old", "\\result", "exists", "forall" };
	private static final FormatVersion FORMAT_VERSION = new FormatVersion(2, 0);

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

	private Witness getWitness() {
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
		final String version = new UltimateCore().getUltimateVersionString();
		final String format = getExpressionFormat();
		final String filename = mTranslatedCFG.getFilename();
		final Supplier<Metadata> metadataSupplier = () -> new Metadata(FORMAT_VERSION, UUID.randomUUID(),
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
				worklist.add(outgoing.getTarget());
				final ILocation loc = (ILocation) outgoing.getLabel();
				if (loc == null) {
					continue;
				}
				// If the column is unknown (-1), use the first position of the line
				final int column = Math.max(loc.getStartColumn(), 0);
				final String function = loc.getFunction();
				if (function == null) {
					// TODO: Is this possible, maybe for global invariants? What is the expected behavior?
					continue;
				}
				locationCandidates.add(new Location(loc.getFileName(), hash, loc.getStartLine(), column, function));
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
		final Witness witness = new Witness(entries);
		switch (FORMAT_VERSION.toString()) {
		case "0.1":
			return witness;
		case "2.0":
			return new Witness(List.of(witness.toInvariantSet(metadataSupplier)));
		default:
			throw new UnsupportedOperationException("Unknown format version " + FORMAT_VERSION);
		}
	}

	public String makeYamlString() {
		return getWitness().toYamlString();
	}

	private String getExpressionFormat() {
		if (!mIsACSLForbidden) {
			throw new UnsupportedOperationException("ACSL is not supported in witnesses yet");
		}
		switch (FORMAT_VERSION.toString()) {
		case "0.1":
			return "C";
		case "2.0":
			return "c_expression";
		default:
			throw new UnsupportedOperationException("Unknown format version " + FORMAT_VERSION);
		}
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
