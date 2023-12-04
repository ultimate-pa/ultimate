package de.uni_freiburg.informatik.ultimate.witnessprinter.yaml;

import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.UUID;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
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
	private final boolean mIsACSLForbidden;
	private final IPreferenceProvider mPreferences;
	private final IIcfg<? extends IcfgLocation> mIcfg;

	public YamlCorrectnessWitnessGenerator(final IIcfg<? extends IcfgLocation> icfg, final ILogger logger,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mIcfg = icfg;
		mPreferences = PreferenceInitializer.getPreferences(services);
		mIsACSLForbidden = mPreferences.getBoolean(PreferenceInitializer.LABEL_DO_NOT_USE_ACSL);
	}

	private Witness getWitness() {
		final String producer = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER);
		final String hash = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PROGRAMHASH);
		final String spec = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_SPECIFICATION);
		final String arch = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_ARCHITECTURE);
		final String version = new UltimateCore().getUltimateVersionString();
		final String format = getExpressionFormat();
		final String filename = ILocation.getAnnotation(mIcfg).getFileName();
		final Supplier<Metadata> metadataSupplier = () -> new Metadata(FORMAT_VERSION, UUID.randomUUID(),
				OffsetDateTime.now(), new Producer(producer, version),
				new Task(List.of(filename), Map.of(filename, hash), spec, arch, "C"));

		final List<IcfgLocation> allProgramPoints = mIcfg.getProgramPoints().values().stream()
				.flatMap(x -> x.values().stream()).collect(Collectors.toList());

		// TODO: Should we sort these entries somehow (for consistent result in validation and to improve readability)
		// e.g. by line number and/or entry type?
		final List<WitnessEntry> entries = extractLoopInvariants(allProgramPoints, metadataSupplier, hash, format);
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

	private List<WitnessEntry> extractLoopInvariants(final List<IcfgLocation> programPoints,
			final Supplier<Metadata> metadataSupplier, final String hash, final String format) {
		final List<WitnessEntry> result = new ArrayList<>();
		for (final IcfgLocation pp : programPoints) {
			final ILocation loc = ILocation.getAnnotation(pp);
			if (loc == null) {
				continue;
			}
			final String invariant = filterInvariant(WitnessInvariant.getAnnotation(pp));
			if (invariant == null) {
				continue;
			}
			// If the column is unknown (-1), use the first position of the line
			final int column = Math.max(loc.getStartColumn(), 0);
			final String function = loc.getFunction();
			if (function == null) {
				// TODO: Is this possible, maybe for global invariants? What is the expected behavior?
				continue;
			}
			final Location witnessLocation =
					new Location(loc.getFileName(), hash, loc.getStartLine(), column, function);
			// TODO: How could we figure out, if it is a LocationInvariant or LoopInvariant?
			// For now we only produce loop invariants anyways
			result.add(new LoopInvariant(metadataSupplier.get(), witnessLocation,
					new Invariant(invariant, "assertion", format)));
		}
		return result;
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

	private String filterInvariant(final WitnessInvariant invariant) {
		if (invariant == null) {
			return null;
		}
		final String label = invariant.getInvariant();
		if (mIsACSLForbidden && label != null && Arrays.stream(ACSL_SUBSTRING).anyMatch(label::contains)) {
			mLogger.warn("Not writing invariant because ACSL is forbidden: " + label);
			return null;
		}
		return label;
	}
}
