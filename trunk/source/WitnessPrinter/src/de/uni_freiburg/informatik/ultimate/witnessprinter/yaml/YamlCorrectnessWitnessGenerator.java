package de.uni_freiburg.informatik.ultimate.witnessprinter.yaml;

import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.UUID;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessProcedureContract;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FunctionContract;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Invariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Metadata;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Producer;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Task;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;
import de.uni_freiburg.informatik.ultimate.witnessprinter.preferences.PreferenceInitializer;

public class YamlCorrectnessWitnessGenerator {
	private static final String[] ACSL_SUBSTRING = new String[] { "\\old", "\\result", "exists", "forall" };

	private final ILogger mLogger;
	private final IPreferenceProvider mPreferences;
	private final IIcfg<? extends IcfgLocation> mIcfg;

	public YamlCorrectnessWitnessGenerator(final IIcfg<? extends IcfgLocation> icfg, final ILogger logger,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mIcfg = icfg;
		mPreferences = PreferenceInitializer.getPreferences(services);
	}

	private Witness getWitness() {
		final String producer = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER);
		final String hash = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PROGRAMHASH);
		final String spec = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_SPECIFICATION);
		final String arch = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_ARCHITECTURE);
		final FormatVersion formatVersion =
				FormatVersion.fromString(mPreferences.getString(PreferenceInitializer.LABEL_YAML_FORMAT_VERSION));
		final String version = new UltimateCore().getUltimateVersionString();
		final String filename = ILocation.getAnnotation(mIcfg).getFileName();
		final Supplier<Metadata> metadataSupplier = () -> new Metadata(formatVersion, UUID.randomUUID(),
				OffsetDateTime.now(), new Producer(producer, version),
				new Task(List.of(filename), Map.of(filename, hash), spec, arch, "C"));

		final List<IcfgLocation> allProgramPoints = mIcfg.getProgramPoints().values().stream()
				.flatMap(x -> x.values().stream()).collect(Collectors.toList());

		// TODO: Should we sort these entries somehow (for consistent result in validation and to improve readability)
		// e.g. by line number and/or entry type?
		final List<WitnessEntry> entries = new ArrayList<>();
		entries.addAll(extractLoopInvariants(allProgramPoints, metadataSupplier, hash, formatVersion));
		if (areACSLAndFunctionContractsAllowed(formatVersion)) {
			entries.addAll(extractFunctionContracts(allProgramPoints, metadataSupplier, hash, formatVersion));
		}
		final Witness witness = new Witness(entries);
		if (formatVersion.getMajor() < 2) {
			return witness;
		}
		return new Witness(List.of(witness.toInvariantSet(metadataSupplier)));
	}

	private static boolean areACSLAndFunctionContractsAllowed(final FormatVersion formatVersion) {
		return formatVersion.compareTo(new FormatVersion(2, 1)) >= 0;
	}

	private List<WitnessEntry> extractLoopInvariants(final List<IcfgLocation> programPoints,
			final Supplier<Metadata> metadataSupplier, final String hash, final FormatVersion formatVersion) {
		final List<WitnessEntry> result = new ArrayList<>();
		for (final IcfgLocation pp : programPoints) {
			final ILocation loc = ILocation.getAnnotation(pp);
			if (loc == null) {
				continue;
			}
			final String invariant = filterInvariant(WitnessInvariant.getAnnotation(pp), formatVersion);
			if (invariant == null) {
				continue;
			}
			final Location witnessLocation = new Location(loc.getFileName(), hash, loc.getStartLine(),
					loc.getStartColumn() < 0 ? null : loc.getStartColumn(), loc.getFunction());
			final Invariant witnessInvariant =
					new Invariant(invariant, "assertion", getExpressionFormat(formatVersion, invariant));
			final LoopEntryAnnotation annot = LoopEntryAnnotation.getAnnotation(pp);
			if (annot != null && annot.getLoopEntryType() == LoopEntryType.WHILE) {
				result.add(new LoopInvariant(metadataSupplier.get(), witnessLocation, witnessInvariant));
			} else {
				result.add(new LocationInvariant(metadataSupplier.get(), witnessLocation, witnessInvariant));
			}
		}
		return result;
	}

	private static List<WitnessEntry> extractFunctionContracts(final List<IcfgLocation> programPoints,
			final Supplier<Metadata> metadataSupplier, final String hash, final FormatVersion formatVersion) {
		final List<WitnessEntry> result = new ArrayList<>();
		for (final IcfgLocation pp : programPoints) {
			final ILocation loc = ILocation.getAnnotation(pp);
			if (loc == null) {
				continue;
			}
			final WitnessProcedureContract contract = WitnessProcedureContract.getAnnotation(pp);
			if (contract == null) {
				continue;
			}
			final String requires = contract.getRequires();
			final String ensures = contract.getEnsures();
			final Location witnessLocation = new Location(loc.getFileName(), hash, loc.getStartLine(),
					loc.getStartColumn() < 0 ? null : loc.getStartColumn(), loc.getFunction());
			result.add(new FunctionContract(metadataSupplier.get(), witnessLocation, requires, ensures,
					getExpressionFormat(formatVersion, requires, ensures)));
		}
		return result;
	}

	public String makeYamlString() {
		return getWitness().toYamlString();
	}

	private static String getExpressionFormat(final FormatVersion formatVersion, final String... expressions) {
		if (formatVersion.getMajor() == 0) {
			return "C";
		}
		if (!areACSLAndFunctionContractsAllowed(formatVersion) || Arrays.stream(expressions).filter(Objects::nonNull)
				.noneMatch(YamlCorrectnessWitnessGenerator::containsACSL)) {
			return "c_expression";
		}
		return "acsl_expression";
	}

	private static boolean containsACSL(final String expression) {
		return Arrays.stream(ACSL_SUBSTRING).anyMatch(expression::contains);
	}

	private String filterInvariant(final WitnessInvariant invariant, final FormatVersion formatVersion) {
		if (invariant == null) {
			return null;
		}
		final String label = invariant.getInvariant();
		if (!areACSLAndFunctionContractsAllowed(formatVersion) && containsACSL(label)) {
			mLogger.warn("Not writing invariant because ACSL is forbidden: " + label);
			return null;
		}
		return label;
	}
}
