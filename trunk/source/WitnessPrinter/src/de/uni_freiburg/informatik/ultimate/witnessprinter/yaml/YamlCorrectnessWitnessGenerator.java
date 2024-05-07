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
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
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
	private final FormatVersion mFormatVersion;
	private final boolean mIsAcslAllowed;
	private final String mProgramHash;
	private final Supplier<Metadata> mMetadataSupplier;
	private final YamlWitnessWriter mWriter;

	public YamlCorrectnessWitnessGenerator(final IIcfg<? extends IcfgLocation> icfg, final ILogger logger,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mIcfg = icfg;
		mPreferences = PreferenceInitializer.getPreferences(services);
		mFormatVersion =
				FormatVersion.fromString(mPreferences.getString(PreferenceInitializer.LABEL_YAML_FORMAT_VERSION));
		mIsAcslAllowed = mFormatVersion.compareTo(new FormatVersion(2, 1)) >= 0;
		final String producer = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER);
		mProgramHash = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PROGRAMHASH);
		final String spec = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_SPECIFICATION);
		final String arch = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_ARCHITECTURE);
		final String version = new UltimateCore().getUltimateVersionString();
		final String filename = ILocation.getAnnotation(mIcfg).getFileName();
		mMetadataSupplier = () -> new Metadata(mFormatVersion, UUID.randomUUID(), OffsetDateTime.now(),
				new Producer(producer, version),
				new Task(List.of(filename), Map.of(filename, mProgramHash), spec, arch, "C"));
		mWriter = YamlWitnessWriter.construct(mFormatVersion, mMetadataSupplier);
	}

	private Witness getWitness() {
		final List<IcfgLocation> allProgramPoints = mIcfg.getProgramPoints().values().stream()
				.flatMap(x -> x.values().stream()).collect(Collectors.toList());
		// TODO: Should we sort these entries somehow (for consistent result in validation and to improve readability)
		// e.g. by line number and/or entry type?
		final var invariants = extractInvariants(allProgramPoints);
		final var functionContracts = extractFunctionContracts(allProgramPoints);
		return new Witness(DataStructureUtils.concat(invariants, functionContracts));
	}

	private List<WitnessEntry> extractInvariants(final List<IcfgLocation> programPoints) {
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
			final Location witnessLocation = new Location(loc.getFileName(), mProgramHash, loc.getStartLine(),
					loc.getStartColumn() < 0 ? null : loc.getStartColumn(), loc.getFunction());
			final Invariant witnessInvariant = new Invariant(invariant, "assertion", getExpressionFormat(invariant));
			final LoopEntryAnnotation annot = LoopEntryAnnotation.getAnnotation(pp);
			if (annot != null && annot.getLoopEntryType() == LoopEntryType.WHILE) {
				result.add(new LoopInvariant(mMetadataSupplier.get(), witnessLocation, witnessInvariant));
			} else {
				result.add(new LocationInvariant(mMetadataSupplier.get(), witnessLocation, witnessInvariant));
			}
		}
		return result;
	}

	private List<WitnessEntry> extractFunctionContracts(final List<IcfgLocation> programPoints) {
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
			final Location witnessLocation = new Location(loc.getFileName(), mProgramHash, loc.getStartLine(),
					loc.getStartColumn() < 0 ? null : loc.getStartColumn(), loc.getFunction());
			result.add(new FunctionContract(mMetadataSupplier.get(), witnessLocation, requires, ensures,
					getExpressionFormat(requires, ensures)));
		}
		return result;
	}

	public String makeYamlString() {
		return mWriter.toString(getWitness());
	}

	private String getExpressionFormat(final String... expressions) {
		if (mFormatVersion.getMajor() == 0) {
			return "C";
		}
		if (!mIsAcslAllowed || Arrays.stream(expressions).filter(Objects::nonNull)
				.noneMatch(YamlCorrectnessWitnessGenerator::containsACSL)) {
			return "c_expression";
		}
		return "acsl_expression";
	}

	private static boolean containsACSL(final String expression) {
		return Arrays.stream(ACSL_SUBSTRING).anyMatch(expression::contains);
	}

	private String filterInvariant(final WitnessInvariant invariant) {
		if (invariant == null) {
			return null;
		}
		final String label = invariant.getInvariant();
		if (!mIsAcslAllowed && containsACSL(label)) {
			mLogger.warn("Not writing invariant because ACSL is forbidden: " + label);
			return null;
		}
		return label;
	}
}
